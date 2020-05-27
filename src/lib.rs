//! # miniintern
//!
//! Minimalistic string interning library.
//!
//! Originally written for `miniecs` string support in component data.
//!
//! <https://ourmachinery.com/post/data-structures-part-3-arrays-of-arrays/>
//!
//! Singlethreaded use - simple:
//! - intern with [`intern`],
//! - lookup with [`lookup`],
//! - remove with [`remove`].
//!
//! Looked up strings may be invalidated on [`remove`] if the internal string storage happens
//! to be defragmented. Rust borrow rules ensure we don't hold on to them as [`remove`] is a
//! mutable method.
//!
//! Multithreaded use - more complex.
//!
//! First, you might want to wrap the [`StringPool`] in a `Mutex` / `RwLock`.
//! However in this case Rust forces the lifetime of the [`looked up`] string to be determined
//! by the lifetime of the `MutexGuard` / `RwLockGuard`, NOT the lifetime of the string pool itself -
//! which defeats the whole point of the string pool.
//!
//! This is the purpose of [`lookup_unsafe`] - an escape hatch which returns the string
//! as a raw pointer with no lifetime associated with it.
//!
//! Second, as stated above, [`remove`] may defragment the string pool in one thread while
//! another thread is holding on to a recently returned string, now pointing to gargbage.
//!
//! This is the purpose of [`remove_gc`] / [`gc`] methods. [`remove_gc`] does not defragment the string
//! pool immediately, but [`gc`] must be called later at a point when only one thread accesses the string pool
//! and no other threads hold on to looked up strings.
//!
//! - in any thread, obtain (write) lock, intern with [`intern`],
//! - in any thread, obtain (read) lock, lookup with [`lookup`],
//! - in any thread, obtain (write) lock, remove with [`remove_gc`],
//!
//! - in some (probably main) thread, when no looked up strings are held by other threads,
//! obtain (write) lock, garbage collect with [`gc`].
//!
//! [`intern`]: struct.StringPool.html#method.intern
//! [`lookup`]: struct.StringPool.html#method.lookup
//! [`looked up`]: struct.StringPool.html#method.lookup
//! [`remove`]: struct.StringPool.html#method.remove
//! [`remove_gc`]: struct.StringPool.html#method.remove_gc
//! [`gc`]: struct.StringPool.html#method.gc
//! [`StringPool`]: struct.StringPool.html
//! [`lookup_unsafe`]: struct.StringPool.html#method.lookup_unsafe

#![allow(clippy::len_without_is_empty)]

use std::collections::{hash_map::DefaultHasher, HashMap};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::error::Error;

/// Unique interned string identifier.
///
/// Internally it's just a string hash (as provided by [`DefaultHasher`]) -
/// so `StringID` equality does not guarantee string equality.
///
/// [`DefaultHasher`]: https://doc.rust-lang.org/nightly/std/collections/hash_map/struct.DefaultHasher.html
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub struct StringID(pub u64);

impl Display for StringID {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// NOTE - maximum chunk size is `std::u16::MAX`, which determines the
/// maximum length in bytes of the string which can be interned by the string pool.
///
/// NOTE - when changing the underlying type, also change the `StringOffset` / `StringLength` types.
pub type ChunkSize = u16;

/// Type for the index of the string chunk in the pool's `chunks` array.
type ChunkIndex = u16;

/// Type for the index of the string in the string chunk's `lookup` array.
type LookupIndex = u16;

/// Type for string offset within the string chunk buffer.
///
/// NOTE - make sure the underlying type matches the `ChunkSize` type above.
type StringOffset = u16;

/// Used to indicate an invalid value for the string chunk free linked list index.
const INVALID_INDEX: StringOffset = StringOffset::MAX;

/// Type for string length within the string chunk buffer.
///
/// NOTE - make sure the underlying type matches the `ChunkSize` type above.
type StringLength = u16;

/// NOTE - we do not allow interning empty strings (and we do allow `u16::MAX` long strings),
/// so we can use `0` as a special value which means an unoccupied string chunk entry.
const INVALID_LENGTH: u16 = 0;

/// Type for the ref count of interned strings.
/// Determines how many copies of a string may be interned before overflow panic.
///
/// NOTE - update the docs for `inern` / `intern_with_id` / `copy` when changing this.
type RefCount = u16;

/// Invalid UTF-8 byte sequence, used to fill the unused space in the string chunks.
#[cfg(debug)]
const CHUNK_FILL_VALUE: u8 = b'\xc0';

/// Manages the collection of unique interned strings.
/// Uses ref-counting internally to deduplicate stored strings.
pub struct StringPool {
    /// Size in bytes of string chunks, allocated by the string pool to store the strings.
    /// Determines the max supported interned string length in bytes.
    chunk_size: ChunkSize,
    /// Maps the string ID / hash to the string indices and ref count.
    lookup: HashMap<StringID, StringState>,
    /// All chunks allocated by the string pool.
    /// Indexed by `StringState::chunk_index`.
    chunks: Vec<StringChunk>,
    /// Cached index of the last chunk a string was successfully interned in,
    /// used to slightly speed up the interning operation.
    last_used_chunk: ChunkIndex,
    /// String ID's of all strings removed from the string pool via `remove_gc` (their ref count reached `0`),
    /// bot not yet garbage collected.
    gc: Vec<StringID>,
}

/// A string represented as a raw pointer + length.
/// Returned by [`lookup_unsafe`].
/// Used as an escape hatch for `MutexGuard<StringPool>` / `RwLockGuard<StringPool>` string lifetime.
///
/// [`lookup_unsafe`]: struct.StringPool.html#method.lookup_unsafe
pub struct UnsafeStr((*const u8, usize));

impl UnsafeStr {
    /// Returns the actual interned string.
    ///
    /// # Safety
    ///
    /// Unsafe because it's up to the user to ensure the string does not outlive the string pool
    /// or is not invalidated by a concurrent call to [`remove`].
    ///
    /// [`remove`]: struct.StringPool.html#method.remove
    pub unsafe fn to_str(&self) -> &'static str {
        std::str::from_utf8_unchecked(std::slice::from_raw_parts((self.0).0, (self.0).1))
    }

    unsafe fn from_str(string: &str) -> Self {
        Self((string.as_ptr(), string.len()))
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum StringPoolError {
    /// Attempted to [`intern`] an empty (zero-length) string.
    /// [`intern`]: struct.StringPool.html#method.intern
    EmptyString,
    /// Attempted to [`intern`] a string whose length in bytes is greater
    /// then the maximum length supported by the [`string pool`]
    /// (as determinded by the `chunk_size` parameter).
    /// Contains the max string length in bytes supported by the [`string pool`]
    /// [`string pool`]: struct.StringPool.html
    /// [`intern`]: struct.StringPool.html#method.intern
    StringTooLong(ChunkSize),
    /// String hash collision detected in the call to [`intern`].
    /// Contains the pair of colliding strings and their hash.
    /// [`intern`]: struct.StringPool.html#method.intern
    HashCollision((String, String, StringID)),
}

impl Error for StringPoolError {}

impl Display for StringPoolError {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        use StringPoolError::*;

        match self{
            EmptyString => write!(f, "attempted to intern an empty (zero-length) string"),
            StringTooLong(chunk_size) => write!(f, "attempted to intern a string whose length in bytes exceeds the chunk size ({}b)", chunk_size),
            HashCollision((str_1, str_2, hash)) => write!(
                f,
                "string hash collision detected: \"{}\" and \"{}\" hash to [{}]",
                str_1, str_2, hash.0
            ),
        }
    }
}

impl StringPool {
    /// Creates a new [`string pool`].
    ///
    /// Interned strings are stored in chunks.
    ///
    /// `chunk_size` determines the max supported interned string length in bytes.
    /// Larger chunks allow for longer strings to be stored, but may have higher memory fragmentation
    /// if the strings are frequently added and removed, as the pool makes no effort to reuse
    /// free space in chunks until it exceeds 50% of the chunks size.
    ///
    /// [`string pool`]: struct.StringPool.html
    pub fn new(chunk_size: ChunkSize) -> Self {
        Self {
            chunk_size,
            lookup: HashMap::new(),
            chunks: Vec::new(),
            last_used_chunk: 0,
            gc: Vec::new(),
        }
    }

    /// Returns the number of unique interned strings in the [`string pool`].
    ///
    /// [`string pool`]: struct.StringPool.html
    pub fn len(&self) -> usize {
        self.lookup.len()
    }

    /// Calculates the [`StringID`] of the `string`.
    /// Guaranteed to be the same as one returned by
    /// [`intern`] would the string be interned via it.
    ///
    /// NOTE - the function returns a default (null) [`StringID`] for empty (zero-length) strings.
    ///
    /// [`StringID`]: struct.StringID.html
    /// [`intern`]: #method.intern
    pub fn string_id(string: &str) -> Result<StringID, StringPoolError> {
        if string.is_empty() {
            Err(StringPoolError::EmptyString)
        } else {
            Ok(StringID(string_hash(string)))
        }
    }

    /// Interns the `string`, returning the [`StringID`]
    /// which may later be used to [`look it up`] or [`remove`] it from the [`string pool`].
    ///
    /// If `string` was already interned, returns the same [`StringID`] as the one returned by the previous call to `intern`,
    /// internally incrementing the string's ref count.
    ///
    /// # Panics
    ///
    /// Panics if the string's ref count overflows (currently, a `u16` is used to store it).
    ///
    /// [`StringID`]: struct.StringID.html
    /// [`look it up`]: #method.lookup
    /// [`remove`]: #method.remove
    /// [`string pool`]: struct.StringPool.html
    pub fn intern(&mut self, string: &str) -> Result<StringID, StringPoolError> {
        let string_id = StringID(string_hash(string));

        unsafe {
            self.intern_with_id(string, string_id)?;
        }

        Ok(string_id)
    }

    /// Interns the `string` using the `string_id`, previously returned for `string` by the call to [`string_id`],
    /// which may later be used to [`look it up`] or [`remove`] it from the [`string pool`].
    ///
    /// If `string` was already interned, internally increments the string's ref count.
    ///
    /// NOTE - meant for use as an optimization in cases where it's possible and beneficial to split [`StringID`] calculation (hashing)
    /// and interning.
    ///
    /// # Safety
    ///
    /// The function is unsafe because the user must guarantee that `string_id` corresponds to `string`.
    ///
    /// # Panics
    ///
    /// In debug mode only, panics if `string_id` does not correspond to `string`.
    /// Panics if the string's ref count overflows (currently, a `u16` is used to store it).
    ///
    /// [`string_id`]: #method.string_id
    /// [`StringID`]: struct.StringID.html
    /// [`look it up`]: #method.lookup
    /// [`remove`]: #method.remove
    /// [`string pool`]: struct.StringPool.html
    pub unsafe fn intern_with_id(
        &mut self,
        string: &str,
        string_id: StringID,
    ) -> Result<(), StringPoolError> {
        let len = string.len();

        if len > self.chunk_size as usize {
            return Err(StringPoolError::StringTooLong(self.chunk_size));
        }

        if len == 0 {
            return Err(StringPoolError::EmptyString);
        }

        let _actual_string_id = StringPool::string_id(string).unwrap();

        debug_assert_eq!(
            _actual_string_id, string_id,
            "`StringID` mismatch: expected {}, found {}.",
            _actual_string_id, string_id
        );

        // The string was interned (but might have been `remove_gc`'d and not yet `gc`'d).
        if let Some(state) = self.lookup.get_mut(&string_id) {
            let looked_up_string = StringPool::lookup_in_chunk(&self.chunks, state.indices);

            // Check for hash collision.
            if looked_up_string != string {
                return Err(StringPoolError::HashCollision((
                    string.to_owned(),
                    looked_up_string.to_owned(),
                    string_id,
                )));
            }

            // NOTE - ref count might have been `0` if the string was `remove_gc`'d and not yet `gc`'d -
            // `gc` will skip strings with non-`0` ref counts.
            state.ref_count = state
                .ref_count
                .checked_add(1)
                .expect("String ref count overflow.");

        // Else the string has not been interned yet.
        } else {
            // Try to intern in the last used chunk.
            let last_used_chunk = self.last_used_chunk as usize;

            if last_used_chunk < self.chunks.len() {
                if let InternResult::Interned(lookup_index) = self
                    .chunks
                    .get_unchecked_mut(last_used_chunk)
                    .intern(string)
                {
                    self.lookup.insert(
                        string_id,
                        StringState::new(last_used_chunk as u16, lookup_index),
                    );
                    return Ok(());
                }
            }

            // If the above failed, try to intern in all chunks in order.
            for (chunk_index, chunk) in self.chunks.iter_mut().enumerate() {
                // Already checked above.
                if chunk_index == last_used_chunk {
                    continue;
                }

                if let InternResult::Interned(lookup_index) = chunk.intern(string) {
                    self.lookup.insert(
                        string_id,
                        StringState::new(chunk_index as u16, lookup_index),
                    );

                    // Update the last used chunk index.
                    self.last_used_chunk = chunk_index as u16;

                    return Ok(());
                }
            }

            // No chunks / no space in all chunks - allocate a new one.
            let mut chunk = StringChunk::new(self.chunk_size);
            let chunk_index = self.chunks.len() as u16;

            // Must succeed.
            match chunk.intern(string) {
                InternResult::Interned(lookup_index) => {
                    self.lookup
                        .insert(string_id, StringState::new(chunk_index, lookup_index));

                    // Update the last used chunk index.
                    self.last_used_chunk = chunk_index;
                }
                _ => unreachable!("Somehow failed to intern a valid length string in an empty string chunk."),
            };

            self.chunks.push(chunk);
        }

        Ok(())
    }

    /// Internally increments the ref count of the string, previously [`intern`]'ed with [`string_id`].
    ///
    /// # Panics
    ///
    /// Panics if the string's ref count overflows (currently, a `u16` is used to store it).
    ///
    /// [`intern`]: #method.intern
    /// [`string_id`]: struct.StringID.html
    pub fn copy(&mut self, string_id: StringID) -> Result<(), ()> {
        // The string was interned (but might have been `remove_gc`'d and not yet `gc`'d).
        if let Some(state) = self.lookup.get_mut(&string_id) {
            // NOTE - ref count might have been `0` if the string was `remove_gc`'d and not yet `gc`'d -
            // `gc` will skip strings with non-`0` ref counts.
            state.ref_count = state
                .ref_count
                .checked_add(1)
                .expect("String ref count overflow.");

            Ok(())
        } else {
            Err(())
        }
    }

    /// Looks up a previously [`intern`]'ed string via its [`string_id`].
    ///
    /// Returns `None` if [`string_id`] does not correspond to a currently interned string.
    ///
    /// [`intern`]: #method.intern
    /// [`string_id`]: struct.StringID.html
    pub fn lookup(&self, string_id: StringID) -> Option<&str> {
        // The string was interned (but might have been `remove_gc`'d and not yet `gc`'d).
        if let Some(state) = self.lookup.get(&string_id) {
            // `remove_gc`'d and not yet `gc`'d.
            if state.ref_count == 0 {
                None
            } else {
                Some(StringPool::lookup_in_chunk(&self.chunks, state.indices))
            }

        // String was not interned, or was already removed.
        } else {
            None
        }
    }

    /// Looks up a previously [`intern`]'ed string via its [`string_id`].
    ///
    /// Returns `None` if [`string_id`] does not correspond to a currently interned string.
    ///
    /// For use in multithreaded scenarios, in conjunction with `Mutex` / `RwLock`.
    ///
    /// # Safety
    ///
    /// Unsafe because the returned string points to the internal memory of the string pool,
    /// which may get overwritten by a concurrent call to [`remove`] - it's up to the
    /// user to ensure [`remove_gc`] / [`gc`] are used instead.
    ///
    /// [`intern`]: #method.intern
    /// [`string_id`]: struct.StringID.html
    /// [`remove`]: #method.remove
    /// [`remove_gc`]: #method.remove_gc
    /// [`gc`]: #method.gc
    pub unsafe fn lookup_unsafe(&self, string_id: StringID) -> Option<UnsafeStr> {
        self.lookup(string_id)
            .map(|string| UnsafeStr::from_str(string))
    }

    /// Internally decrements the ref count associated with the [`string_id`] of a previously [`intern`]'ed string.
    ///
    /// When the ref count reaches zero, the string is removed from the pool - it may no longer be [`looked up`].
    /// May invalidate the previously [`looked up`] strings.
    ///
    /// Does nothing if [`string_id`] does not correspond to a currently [`intern`]'ed string.
    ///
    /// [`intern`]: #method.intern
    /// [`string_id`]: struct.StringID.html
    /// [`looked up`]: #method.lookup_unsafe
    pub fn remove(&mut self, string_id: StringID) -> Result<(), ()> {
        // The string was interned (but might have been `remove_gc`'d and not yet `gc`'d).
        if let Some(state) = self.lookup.get_mut(&string_id) {
            // `remove_gc`'d and not yet `gc`'d.
            if state.ref_count == 0 {
                return Err(())

            } else {
                state.ref_count -= 1;

                // This was the last use of this string - remove it from the chunk.
                if state.ref_count == 0 {
                    StringPool::remove_from_chunk(
                        state.indices,
                        &mut self.chunks,
                        &mut self.lookup,
                    );

                    self.lookup.remove(&string_id);
                }
            }
        } else {
            return Err(());
        }

        Ok(())
    }

    /// Internally decrements the ref count associated with the [`string_id`] of a previously [`intern`]'ed string.
    ///
    /// When the ref count reaches zero, the string is marked for removal from the pool,
    /// but its memory is not immediately cleaned up - it may no longer be [`looked up`],
    /// but does not invalidate the previously [`looked up`] strings.
    ///
    /// A call to [`gc`] is required to actually free the memory of strings removed via this method.
    ///
    /// Does nothing if [`string_id`] does not correspond to a currently interned string.
    ///
    /// [`intern`]: #method.intern
    /// [`string_id`]: struct.StringID.html
    /// [`looked up`]: #method.lookup
    /// [`gc`]: #method.gc
    pub fn remove_gc(&mut self, string_id: StringID) -> Result<(), ()> {
        // The string was interned (but might have been `remove_gc`'d and not yet `gc`'d).
        if let Some(state) = self.lookup.get_mut(&string_id) {
            // Looks like we called this method more times than `intern` / `copy`,
            // and `lookup` has not been updated yet by a call to `gc`.
            if state.ref_count == 0 {
                Err(())
            } else {
                state.ref_count -= 1;

                if state.ref_count == 0 {
                    self.gc.push(string_id);
                }

                Ok(())
            }
        } else {
            Err(())
        }
    }

    /// Frees the memory of the strings, previously removed via [`remove_gc`].
    ///
    /// May invalidate the previously [`looked up`] strings.
    ///
    /// [`remove_gc`]: #method.remove_gc
    /// [`looked up`]: #method.lookup
    pub fn gc(&mut self) {
        while let Some(string_id) = self.gc.pop() {
            let state = self
                .lookup
                .get(&string_id)
                .expect("Invalid GC'd string ID.");

            // The string might be in the `gc` array, but have since been re-inerned / copied,
            // which would increment its ref count - we skip these here.
            if state.ref_count == 0 {
                StringPool::remove_from_chunk(
                    state.indices,
                    &mut self.chunks,
                    &mut self.lookup,
                );

                let removed = self.lookup.remove(&string_id);
                debug_assert!(removed.is_some());
            }
        }
    }

    /// Given an array of string chunks and the string indices, looks up the string.
    /// NOTE - the caller guarantees the `indices` are valid, so the call always succeeds.
    fn lookup_in_chunk(chunks: &[StringChunk], indices: StringIndices) -> &str {
        let chunk_index = indices.chunk_index as usize;
        debug_assert!(chunk_index < chunks.len());
        unsafe { chunks.get_unchecked(chunk_index) }.lookup(indices.lookup_index)
    }

    /// Given the array of string chunks, the string lookup table and the string indices,
    /// removes the string from its chunk and updates the lookup table.
    /// NOTE - the caller guarantees the `indices` are valid, so the call always succeeds.
    fn remove_from_chunk(
        indices: StringIndices,
        chunks: &mut Vec<StringChunk>,
        lookup: &mut HashMap<StringID, StringState>,
    ) {
        let chunk_index = indices.chunk_index as usize;
        debug_assert!(chunk_index < chunks.len());

        if let RemoveResult::ChunkFree =
            unsafe { chunks.get_unchecked_mut(chunk_index) }.remove(indices.lookup_index)
        {
            // The chunk is completely empty - we just free it immediately.
            let last_chunk_index = (chunks.len() - 1) as u16;

            // Remove the chunk by swapping it with the last one.
            let free_chunk = chunks.swap_remove(chunk_index);
            std::mem::drop(free_chunk);

            // Patch the chunk indices referring to the now moved last chunk, if necessary.
            if last_chunk_index as usize != chunk_index {
                for state in lookup.iter_mut().filter_map(|(_, v)| {
                    if v.indices.chunk_index == last_chunk_index {
                        Some(v)
                    } else {
                        None
                    }
                }) {
                    state.indices.chunk_index = chunk_index as u16;
                }
            }
        }
    }
}

/// Describes the interned string location in the string pool.
#[derive(Clone, Copy)]
struct StringIndices {
    /// Index of the chunk in which the string is interned.
    /// These must be patched up whenever a chunk is moved in the chunk array
    /// (i.e. when a non-last chunk is removed via erase-swap when it becomes empty).
    chunk_index: ChunkIndex,
    /// Index of the element in the chunk's `lookup` array,
    /// which contains this string's offset from the chunk's start and its length.
    lookup_index: LookupIndex,
}

/// Interned string descriptor.
#[derive(Clone, Copy)]
struct StringState {
    /// Ref count of the interned string.
    ref_count: RefCount,
    indices: StringIndices,
}

impl StringState {
    fn new(chunk_index: ChunkIndex, lookup_index: LookupIndex) -> Self {
        Self {
            ref_count: 1,
            indices: StringIndices {
                chunk_index,
                lookup_index,
            }
        }
    }
}

/// Describes the interned string slice's location in the string chunk.
#[derive(Clone, Copy)]
struct StringInChunk {
    /// String start offset in bytes from `data` array start.
    /// Also used as the lookup array entry free list node, or `INVALID_INDEX`.
    offset: StringOffset,
    /// (non-null) string length in bytes.
    length: StringLength,
}

/// A fixed-size memory chunk used to store interned strings.
struct StringChunk {
    /// Size of `data` array in bytes.
    /// Needed for `free`.
    /// TODO: remove this.
    chunk_size: ChunkSize,
    /// Num of bytes in `data` array containing string bytes.
    occupied_bytes: ChunkSize,
    /// First free byte in the `data` array.
    first_free_byte: StringOffset,
    /// Starts `false`.
    /// Set to `true` when interning, whenever occupancy reaches >50%.
    /// Set to `false` when removing, whenever occupancy reaches <50% and the chunk is defragmented.
    fragmented: bool,
    /// Lookup array which maps `StringState::lookup_index` to string offsets/lengths within the chunk data buffer.
    lookup: Vec<StringInChunk>,
    /// First free index in the lookup array, or `INVALID_INDEX`.
    /// Free lookup array entries form a linked list via their `offset` field.
    first_free_index: StringOffset,
    /// The chunk's string data buffer.
    data: *mut u8,
}

impl Drop for StringChunk {
    fn drop(&mut self) {
        free(self.data, self.chunk_size as usize);
    }
}

enum InternResult {
    /// Not enough free space left in the chunk.
    NoSpace,
    /// Successfully interned the string.
    /// Contains the index of the string in the chunk's lookup array.
    Interned(LookupIndex),
}

enum RemoveResult {
    /// Chunk still has some strings in it.
    ChunkInUse,
    /// Chunk is completely empty and may be freed.
    ChunkFree,
}

impl StringChunk {
    fn new(chunk_size: ChunkSize) -> Self {
        Self {
            chunk_size,
            occupied_bytes: 0,
            first_free_byte: 0,
            fragmented: false,
            lookup: Vec::new(),
            first_free_index: INVALID_INDEX,
            #[cfg(debug)]
            data: malloc(chunk_size as usize, CHUNK_FILL_VALUE),
            #[cfg(not(debug))]
            data: malloc(chunk_size as usize, 0),
        }
    }

    /// Tries to intern the string in this chunk.
    fn intern(&mut self, string: &str) -> InternResult {
        // NOTE - guaranteed to fit in `u16` by the calling code.
        let length = string.len() as StringLength;

        debug_assert!(self.chunk_size >= self.first_free_byte);
        let remaining_bytes = self.chunk_size - self.first_free_byte;

        // Not enough space.
        if length > remaining_bytes {
            return InternResult::NoSpace;
        }

        let offset = self.first_free_byte;

        // Get the lookup index from the free list, or allocate a new element.
        let lookup_index = if self.first_free_index != INVALID_INDEX {
            let lookup_index = self.first_free_index as usize;
            debug_assert!(lookup_index < self.lookup.len());
            let string_in_chunk = unsafe { self.lookup.get_unchecked_mut(lookup_index) };
            self.first_free_index = string_in_chunk.offset;
            string_in_chunk.offset = offset;
            string_in_chunk.length = length;
            lookup_index as LookupIndex
        } else {
            let lookup_index = self.lookup.len() as LookupIndex;
            self.lookup.push(StringInChunk { offset, length });
            lookup_index
        };

        self.first_free_byte += length;

        self.occupied_bytes += length;
        debug_assert!(self.occupied_bytes <= self.chunk_size);

        // If we were defragmented and are now >50% occupancy -
        // mark the chunk as fragmented.
        if !self.fragmented && (self.occupied_bytes > (self.chunk_size / 2)) {
            self.fragmented = true;
        }

        let src = string.as_bytes().as_ptr();
        let dst = unsafe { self.data.offset(offset as isize) };

        unsafe {
            std::ptr::copy_nonoverlapping(src, dst, length as usize);
        }

        InternResult::Interned(lookup_index)
    }

    /// Looks up the string in this chunk given its `lookup_index`.
    /// NOTE - the caller guarantees `lookup_index` is valid, so the call always succeeds.
    fn lookup(&self, lookup_index: LookupIndex) -> &str {
        let lookup_index = lookup_index as usize;
        debug_assert!(lookup_index < self.lookup.len());
        let string_in_chunk = unsafe { self.lookup.get_unchecked(lookup_index) };
        debug_assert!(string_in_chunk.offset < self.chunk_size);
        debug_assert!(string_in_chunk.length <= self.chunk_size);

        unsafe {
            let src = self.data.offset(string_in_chunk.offset as isize);
            let slice = std::slice::from_raw_parts(src, string_in_chunk.length as usize);
            #[cfg(debug)]
            {
                std::str::from_utf8_unchecked(slice)
            }
            #[cfg(not(debug))]
            {
                std::str::from_utf8(slice).unwrap()
            }
        }
    }

    /// Removes the string from this chunk given its `lookup_index`.
    /// NOTE - the caller guarantees `lookup_index` is valid, so the call always succeeds.
    fn remove(&mut self, lookup_index: LookupIndex) -> RemoveResult {
        debug_assert!((lookup_index as usize) < self.lookup.len());
        let string_in_chunk = unsafe { self.lookup.get_unchecked_mut(lookup_index as usize) };
        debug_assert!(string_in_chunk.offset < self.chunk_size);
        debug_assert!(string_in_chunk.length <= self.chunk_size);

        // Fill the now empty space with garbage.
        #[cfg(debug)]
        unsafe {
            let dst = self.data.offset(string_in_chunk.offset as isize);
            std::ptr::write_bytes(dst, CHUNK_FILL_VALUE, string_in_chunk.length as usize);
        }

        debug_assert!(self.occupied_bytes >= string_in_chunk.length);
        self.occupied_bytes -= string_in_chunk.length;

        if self.occupied_bytes == 0 {
            return RemoveResult::ChunkFree;
        }

        // Put this lookup entry on the free list.
        string_in_chunk.offset = self.first_free_index;
        string_in_chunk.length = INVALID_LENGTH;
        self.first_free_index = lookup_index;

        // Defragment if <50% occupied and not already defragmented.
        if self.fragmented && (self.occupied_bytes < self.chunk_size / 2) {
            // Gather the string ranges.
            // Tuples of (current string offset/length, new string offset).
            let mut string_offsets = self.lookup.iter()
                .filter_map(|string_in_chunk| {
                    // Skip the free entries.
                    if string_in_chunk.length == INVALID_LENGTH {
                        None
                    } else {
                        Some((*string_in_chunk, 0))
                    }
                })
                .collect::<Vec<_>>();

            // Sanity check - string lengths must add up to chunk's occupied bytes.
            debug_assert_eq!(
                string_offsets
                    .iter()
                    .fold(0, |sum, el| { sum + el.0.length }),
                self.occupied_bytes
            );

            // Sort by current offset.
            string_offsets.sort_by(|l, r| l.0.offset.cmp(&r.0.offset));

            // Compact.
            let mut offset = 0;

            for (string_in_chunk, new_offset) in string_offsets.iter_mut() {
                unsafe {
                    let src = self.data.offset(string_in_chunk.offset as isize);
                    let dst = self.data.offset(offset as isize);

                    // May overlap.
                    std::ptr::copy(src, dst, string_in_chunk.length as usize);

                    *new_offset = offset;
                    offset += string_in_chunk.length;
                }
            }
            debug_assert_eq!(offset, self.occupied_bytes);

            // Move the free pointer back.
            self.first_free_byte = self.occupied_bytes;

            // Fill the now free space with garbage.
            #[cfg(debug)]
            {
                let remaining_bytes = self.chunk_size - self.first_free_byte;

                if remaining_bytes > 0 {
                    unsafe {
                        let dst = self.data.offset(self.first_free_byte as isize);

                        std::ptr::write_bytes(dst, CHUNK_FILL_VALUE, remaining_bytes as usize);
                    }
                }
            }

            // Patch the string offsets.
            for (new_string, new_offset) in string_offsets.iter() {
                let found = self
                    .lookup
                    .iter_mut()
                    .find(|old_string| old_string.offset == new_string.offset)
                    .unwrap();
                found.offset = *new_offset;
            }

            self.fragmented = false;
        }

        RemoveResult::ChunkInUse
    }
}

fn string_hash(string: &str) -> u64 {
    let mut hasher = DefaultHasher::new();
    string.hash(&mut hasher);
    hasher.finish()
}

fn malloc(size: usize, val: u8) -> *mut u8 {
    let mut vec = vec![val; size];
    let ptr = vec.as_mut_ptr();
    std::mem::forget(vec);
    ptr
}

fn free(ptr: *mut u8, size: usize) {
    let vec = unsafe { Vec::from_raw_parts(ptr, size, size) };
    std::mem::drop(vec);
}