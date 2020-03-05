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

/// Manages the collection of unique interned strings.
/// Uses ref-counting internally to deduplicate stored strings.
pub struct StringPool {
    chunk_size: ChunkSize,
    lookup: HashMap<StringID, StringState>,
    chunks: Vec<StringChunk>,
    last_used_chunk: u16,
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

    fn from_str(string: &str) -> Self {
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

impl Display for StringPoolError {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        use StringPoolError::*;

        match self{
            EmptyString => write!(f, "Attempted to intern an empty (zero-length) string."),
            StringTooLong(chunk_size) => write!(f, "Attempted to intern a string whose length in bytes is greater than the chunk size ({}b).", chunk_size),
            HashCollision((str_1, str_2, hash)) => write!(
                f,
                "String hash collision detected: \"{}\" and \"{}\" hash to [{}]",
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
    pub fn string_id(string: &str) -> StringID {
        if string.is_empty() {
            StringID::default()
        } else {
            StringID(string_hash(string))
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
        let len = string.len();

        if len > self.chunk_size as usize {
            return Err(StringPoolError::StringTooLong(self.chunk_size));
        }

        if len == 0 {
            return Err(StringPoolError::EmptyString);
        }

        let string_id = StringID(string_hash(string));

        unsafe {
            self.intern_with_id(string, string_id).unwrap();
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

        let _actual_string_id = StringPool::string_id(string);

        debug_assert_eq!(
            _actual_string_id, string_id,
            "`StringID` mismatch: expected {}, found {}.",
            _actual_string_id, string_id
        );

        // String was already interned.
        if let Some(state) = self.lookup.get_mut(&string_id) {
            // Check for hash collision.
            let looked_up_string = StringPool::lookup_in_state(&self.chunks, *state).unwrap();

            if looked_up_string != string {
                return Err(StringPoolError::HashCollision((
                    string.to_owned(),
                    looked_up_string.to_owned(),
                    string_id,
                )));
            }

            state.ref_count = state
                .ref_count
                .checked_add(1)
                .expect("String ref count overflow.");

        // Else the string has not been interned yet.
        } else {
            // Try to intern in the last used chunk.
            let last_used_chunk = self.last_used_chunk as usize;

            if last_used_chunk < self.chunks.len() {
                if let InternResult::Interned(lookup_index) =
                    self.chunks[last_used_chunk].intern(string)
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
                _ => unreachable!(),
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
        // String was interned.
        if let Some(state) = self.lookup.get_mut(&string_id) {
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
            StringPool::lookup_in_state(&self.chunks, *state)

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
    /// [`remove`]: struct.StringPool.html#method.remove
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
        // String was interned.
        if let Some(state) = self.lookup.get_mut(&string_id) {
            debug_assert!(state.ref_count > 0);
            state.ref_count -= 1;

            // This was the last use of this string - remove it from the chunk.
            if state.ref_count == 0 {
                StringPool::remove_from_chunk(
                    state.chunk_index,
                    state.lookup_index,
                    &mut self.chunks,
                    &mut self.lookup,
                );

                self.lookup.remove(&string_id);
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
        // String was interned.
        if let Some(state) = self.lookup.get_mut(&string_id) {
            if state.ref_count > 0 {
                state.ref_count -= 1;
                self.gc.push(string_id);

                Ok(())

            // Looks like we called this method more times than `intern` / `copy`,
            // and `lookup` has not been updated yet by a call to `gc`.
            } else {
                Err(())
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

            // If the ref count is non-null, the same string has been reinterned.
            // Otherwise we clean it up.
            if state.ref_count == 0 {
                StringPool::remove_from_chunk(
                    state.chunk_index,
                    state.lookup_index,
                    &mut self.chunks,
                    &mut self.lookup,
                );

                self.lookup.remove(&string_id);
            }
        }
    }

    // NOTE - the caller guarantees `chunk_index` and `lookup_index` are valid.
    fn lookup_in_chunk(chunks: &[StringChunk], chunk_index: u16, lookup_index: u16) -> &str {
        let chunk_index = chunk_index as usize;
        debug_assert!(chunk_index < chunks.len());
        chunks[chunk_index].lookup(lookup_index)
    }

    fn lookup_in_state(chunks: &[StringChunk], state: StringState) -> Option<&str> {
        // If the ref count is `0`, the string was removed but not yet garbage collected.
        if state.ref_count == 0 {
            None
        } else {
            Some(StringPool::lookup_in_chunk(
                chunks,
                state.chunk_index,
                state.lookup_index,
            ))
        }
    }

    // NOTE - the caller guarantees `chunk_index` and `lookup_index` are valid.
    fn remove_from_chunk(
        chunk_index: ChunkIndex,
        lookup_index: LookupIndex,
        chunks: &mut Vec<StringChunk>,
        lookup: &mut HashMap<StringID, StringState>,
    ) {
        let chunk_index = chunk_index as usize;
        debug_assert!(chunk_index < chunks.len());

        if let RemoveResult::ChunkFree = chunks[chunk_index].remove(lookup_index) {
            // The chunk is completely empty - we just free it immediately.
            let last_chunk_index = (chunks.len() - 1) as u16;

            // Remove the chunk by swapping it with the last one.
            let free_chunk = chunks.swap_remove(chunk_index);
            std::mem::drop(free_chunk);

            // Patch the chunk indices referring to the now moved last chunk, if necessary.
            if last_chunk_index as usize != chunk_index {
                for state in lookup.iter_mut().filter_map(|(_, v)| {
                    if v.chunk_index == last_chunk_index {
                        Some(v)
                    } else {
                        None
                    }
                }) {
                    state.chunk_index = chunk_index as u16;
                }
            }
        }
    }
}

type ChunkIndex = u16;
type LookupIndex = u16;

/// Interned string descriptor.
#[derive(Clone, Copy)]
struct StringState {
    /// Ref count of the interned string.
    ref_count: u16,
    /// Index of the chunk in which the string is interned.
    chunk_index: ChunkIndex,
    /// Index of the element in the chunk's offset lookup array
    /// which contains this string's offset from the chunk's start and its length.
    lookup_index: LookupIndex,
}

impl StringState {
    fn new(chunk_index: ChunkIndex, lookup_index: LookupIndex) -> Self {
        Self {
            ref_count: 1,
            chunk_index,
            lookup_index,
        }
    }
}

/// NOTE - make sure the underlying type matches the `ChunkSize` type above.
type StringOffset = u16;
type StringLength = u16;

/// Describes the interned string slice's location in the string chunk.
#[derive(Clone, Copy)]
struct StringInChunk {
    /// String start offset in bytes from `data` array start.
    /// Also used as the lookup array entry free list node.
    offset: StringOffset,
    /// String length in bytes.
    length: StringLength,
}

/// A fixed-size memory chunk used to store interned strings.
struct StringChunk {
    /// Size of `data` array in bytes.
    chunk_size: ChunkSize,
    /// Num of bytes in `data` array containing string bytes.
    occupied_bytes: ChunkSize,
    /// First free byte in the `data` array.
    first_free_byte: StringOffset,
    /// Starts `false`.
    /// Set to `true` when interning, whenever occupancy reaches >50%.
    /// Set to `false` when removing, whenever occupancy reaches <50% and the chunk is defragmented.
    fragmented: bool,
    /// Lookup array for string offsets/lengths.
    lookup: Vec<StringInChunk>,
    /// First free index in the lookup array, or `std::u16::MAX`.
    /// Free lookup array entries form a linked list via their `offset` field.
    first_free_index: u16,
    /// The chunk's string data array.
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
            first_free_index: std::u16::MAX,
            // Invalid UTF-8 byte sequence.
            data: malloc(chunk_size as usize, b'\xc0'),
        }
    }

    fn intern(&mut self, string: &str) -> InternResult {
        // NOTE - guaranteed to fit in `u16` by the calling code.
        let length = string.len() as StringLength;

        let remaining_bytes = self.chunk_size - self.first_free_byte;

        // Not enough space.
        if length > remaining_bytes {
            return InternResult::NoSpace;
        }

        let offset = self.first_free_byte;

        // Get the lookup index from the free list, or allocate a new element.
        let lookup_index = if self.first_free_index != std::u16::MAX {
            let lookup_index = self.first_free_index;
            debug_assert!((lookup_index as usize) < self.lookup.len());
            let string_in_chunk = &mut self.lookup[lookup_index as usize];
            self.first_free_index = string_in_chunk.offset;
            string_in_chunk.offset = offset;
            string_in_chunk.length = length;
            lookup_index
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

    // NOTE - the caller guarantees `lookup_index` is valid.
    fn lookup(&self, lookup_index: LookupIndex) -> &str {
        let lookup_index = lookup_index as usize;
        debug_assert!(lookup_index < self.lookup.len());
        let string_in_chunk = &self.lookup[lookup_index];
        debug_assert!(string_in_chunk.offset < self.chunk_size);
        debug_assert!(string_in_chunk.length <= self.chunk_size);

        unsafe {
            let src = self.data.offset(string_in_chunk.offset as isize);
            let slice = std::slice::from_raw_parts(src, string_in_chunk.length as usize);
            std::str::from_utf8_unchecked(slice)
        }
    }

    // NOTE - the caller guarantees `lookup_index` is valid.
    fn remove(&mut self, lookup_index: LookupIndex) -> RemoveResult {
        debug_assert!((lookup_index as usize) < self.lookup.len());
        let string_in_chunk = &mut self.lookup[lookup_index as usize];
        debug_assert!(string_in_chunk.offset < self.chunk_size);
        debug_assert!(string_in_chunk.length <= self.chunk_size);

        unsafe {
            let dst = self.data.offset(string_in_chunk.offset as isize);

            // Invalid UTF-8 byte sequence.
            std::ptr::write_bytes(dst, b'\xc0', string_in_chunk.length as usize);
        }

        debug_assert!(self.occupied_bytes >= string_in_chunk.length);
        self.occupied_bytes -= string_in_chunk.length;

        if self.occupied_bytes == 0 {
            return RemoveResult::ChunkFree;
        }

        // Put this lookup entry on the free list.
        string_in_chunk.offset = self.first_free_index;
        string_in_chunk.length = std::u16::MAX;
        self.first_free_index = lookup_index;

        // Defragment if <50% occupied and not already defragmented.
        if self.fragmented && (self.occupied_bytes < self.chunk_size / 2) {
            // Gather string ranges.
            // Tuples of (current string offset/length, new string offset).
            let mut current_strings = Vec::new();

            for string_in_chunk in self.lookup.iter() {
                // Skip the free entries.
                if string_in_chunk.length == std::u16::MAX {
                    continue;
                }

                current_strings.push((*string_in_chunk, 0));
            }

            // Sanity check - string lengths must add up to chunk's occupied bytes.
            debug_assert_eq!(
                current_strings
                    .iter()
                    .fold(0, |sum, el| { sum + el.0.length }),
                self.occupied_bytes
            );

            // Sort by offset.
            current_strings.sort_by(|l, r| l.0.offset.cmp(&r.0.offset));

            // Compact.
            let mut offset = 0;

            for (string_in_chunk, new_offset) in current_strings.iter_mut() {
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

            // Fill the free space with UTF-8 garbage.
            let remaining_bytes = self.chunk_size - self.first_free_byte;

            if remaining_bytes > 0 {
                unsafe {
                    let dst = self.data.offset(self.first_free_byte as isize);

                    // Invalid UTF-8 byte sequence.
                    std::ptr::write_bytes(dst, b'\xc0', remaining_bytes as usize);
                }
            }

            // Patch the offsets.
            for (string_in_chunk, new_offset) in current_strings.iter() {
                let found = self
                    .lookup
                    .iter_mut()
                    .find(|el| el.offset == string_in_chunk.offset)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        const CHUNK_SIZE: ChunkSize = 8;

        let mut pool = StringPool::new(CHUNK_SIZE);

        // Empty strings.
        let empty = "";
        assert_eq!(
            pool.intern(empty).unwrap_err(),
            StringPoolError::EmptyString
        );

        let asdf = "asdf";
        let gh = "gh";

        let asdf_id = pool.intern(asdf).unwrap();
        assert_eq!(asdf_id.0, string_hash(asdf));
        assert_eq!(asdf_id, StringPool::string_id(asdf));

        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        // Should not allocate new data.
        let asdf_id_2 = pool.intern(asdf).unwrap();
        assert_eq!(asdf_id, asdf_id_2);

        assert_eq!(pool.lookup(asdf_id_2).unwrap(), asdf);

        // This decrements the ref count.
        pool.remove(asdf_id_2).unwrap();

        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        // This increments the ref count.
        pool.copy(asdf_id).unwrap();

        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        // This decrements the ref count.
        pool.remove(asdf_id).unwrap();

        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        let gh_id = StringPool::string_id(gh);
        assert_eq!(gh_id.0, string_hash(gh));

        unsafe {
            pool.intern_with_id(gh, gh_id).unwrap();
        }

        assert_eq!(pool.lookup(gh_id).unwrap(), gh);

        assert!(gh_id != asdf_id);

        let asdf_unsafe = unsafe { pool.lookup_unsafe(asdf_id).unwrap() };

        unsafe {
            assert_eq!(asdf_unsafe.to_str(), asdf);
        }

        // Should not trigger defragmentation.
        pool.remove_gc(asdf_id).unwrap();

        // The string may not be looked up any more.
        assert!(pool.lookup(asdf_id).is_none());

        // But the string data is still there.
        unsafe {
            assert_eq!(asdf_unsafe.to_str(), asdf);
        }

        // Now defragmentation happens, `asdf_unsafe` contains garbage.
        pool.gc();

        assert!(pool.lookup(asdf_id).is_none());
        assert_eq!(pool.lookup(gh_id).unwrap(), gh);

        let asdf_id = pool.intern(asdf).unwrap();
        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        // Should allocate a new chunk.
        let long_string = "asdfghjk";

        let long_string_id = pool.intern(long_string).unwrap();

        assert_eq!(pool.lookup(long_string_id).unwrap(), long_string);

        // Should free the first chunk.
        pool.remove(gh_id).unwrap();

        assert!(pool.lookup(gh_id).is_none());

        assert_eq!(pool.lookup(long_string_id).unwrap(), long_string);

        // Should free the last chunk.
        pool.remove(long_string_id).unwrap();

        // String is too long.
        let very_long_string = "asdfghjkl";
        assert_eq!(
            pool.intern(very_long_string).unwrap_err(),
            StringPoolError::StringTooLong(8)
        );
    }
}
