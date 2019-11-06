//! # miniintern
//!
//! Minimalistic string interning library.
//!
//! Originally written for `miniecs` string support in component data.
//!
//! TODO:
//! - hash collisions are detected via a panic in debug mode, but not release.
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

use std::collections::{hash_map::DefaultHasher, HashMap};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};

/// Unique interned string identifier.
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

/// Manages the collection of unique interned strings.
/// Uses ref-counting internally to deduplicate stored strings.
pub struct StringPool {
    chunk_size: u16,
    lookup: HashMap<StringID, StringState>,
    chunks: Vec<StringChunk>,
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
    pub unsafe fn to_str(&self) -> &str {
        std::str::from_utf8_unchecked(std::slice::from_raw_parts((self.0).0, (self.0).1))
    }

    fn from_str(string: &str) -> Self {
        Self((string.as_ptr(), string.len()))
    }
}

impl StringPool {
    /// Creates a new string pool.
    ///
    /// Interned strings are stored in chunks.
    ///
    /// `chunk_size` determines the max supported interned string length in bytes.
    /// Larger chunks allow for longer strings to be stored, but may have higher memory fragmentation
    /// if the strings are frequently added and removed, as the pool makes no effort to reuse
    /// free space in chunks until it exceeds 50% of the chunks size.
    pub fn new(chunk_size: u16) -> Self {
        Self {
            chunk_size,
            lookup: HashMap::new(),
            chunks: Vec::new(),
            gc: Vec::new(),
        }
    }

    /// Calculates the [`StringID`] of the `string`, guaranteed to be the same as one returned by
    /// [`intern`] would the string be interned via it.
    ///
    /// NOTE - the function returns a default (null) [`StringID`] for empty (zero-length) strings.
    ///
    /// [`StringID`]: struct.StringID.html
    /// [`intern`]: #method.intern
    pub fn string_id(string: &str) -> StringID {
        if string.len() == 0 {
            StringID::default()
        } else {
            StringID(string_hash(string))
        }
    }

    /// Interns the string, returning the [`StringID`] which may be used to look it up or remove it from the pool.
    ///
    /// If `string` was laready interned, returns the same [`StringID`] as the one returned by the previous call to `intern`,
    /// internally incrementing the string's ref count.
    ///
    /// NOTE - empty (zero-length) strings are NOT interned, the function returns a default (null) [`StringID`].
    ///
    /// # Panics
    ///
    /// Panics if `string` length exceeds `chunk_size` bytes.
    /// In debug mode only, panics on hash collision (same `StringID` generated for non-equal strings).
    ///
    /// [`StringID`]: struct.StringID.html
    pub fn intern(&mut self, string: &str) -> StringID {
        assert!(
            string.len() <= self.chunk_size as usize,
            "Max supported interned string length in bytes is `{}` - tried to intern `{}` bytes.",
            self.chunk_size,
            string.len()
        );

        if string.len() == 0 {
            return StringID::default();
        }

        let string_id = StringID(string_hash(string));

        unsafe {
            self.intern_with_id(string, string_id);
        }

        string_id
    }

    /// Interns the string using the `string_id`, previously returned for `string` by the call to [`string_id`],
    /// which may be used to look it up or remove it from the pool.
    /// If `string` was laready interned, internally increments the string's ref count.
    ///
    /// NOTE - empty (zero-length) strings are NOT interned.
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
    /// Panics if `string` length exceeds `chunk_size` bytes.
    /// In debug mode only, panics on hash collision (same `StringID` generated for non-equal strings).
    ///
    /// [`string_id`]: #method.string_id
    /// [`StringID`]: struct.StringID.html
    pub unsafe fn intern_with_id(&mut self, string: &str, string_id: StringID) {
        if string.len() == 0 {
            return;
        }

        debug_assert_eq!(
            StringPool::string_id(string),
            string_id,
            "String / StringID mismatch: expected {}, found {}.",
            StringPool::string_id(string),
            string_id
        );

        // String was already interned.
        if let Some(state) = self.lookup.get_mut(&string_id) {
            state.ref_count += 1;

            // Debug-only hash collision detection - just a panic.
            // TODO - fix this.
            debug_assert_eq!(
                string,
                self.lookup(string_id).unwrap(),
                "Hash collision detected. Interned: \"{}\", new: \"{}\", hash: [{}].",
                self.lookup(string_id).unwrap(),
                string,
                string_id.0
            );

        // Else the string has not been interned yet.
        } else {
            // Try to intern in all chunks in order.
            for (chunk_index, chunk) in self.chunks.iter_mut().enumerate() {
                match chunk.intern(string) {
                    InternResult::Interned(lookup_index) => {
                        let new_state = StringState::new(chunk_index as u16, lookup_index);
                        self.lookup.insert(string_id, new_state);
                    }
                    _ => {}
                }
            }

            // No chunks / no space in all chunks - allocate a new one.
            let mut chunk = StringChunk::new(self.chunk_size);
            let chunk_index = self.chunks.len();

            // Must succeed.
            match chunk.intern(string) {
                InternResult::Interned(lookup_index) => {
                    let new_state = StringState::new(chunk_index as u16, lookup_index);
                    self.lookup.insert(string_id, new_state);
                }
                _ => unreachable!(),
            };

            self.chunks.push(chunk);
        }
    }

    /// Looks up a previously [`intern`]'ed string via its [`StringID`].
    ///
    /// Returns `None` if `string_id` does not correspond to a currently interned string.
    ///
    /// [`intern`]: #method.intern
    /// [`StringID`]: struct.StringID.html
    pub fn lookup(&self, string_id: StringID) -> Option<&str> {
        // String was interned.
        if let Some(state) = self.lookup.get(&string_id) {
            // If the ref count is `0`, the string was removed but not yet garbage collected.
            if state.ref_count > 0 {
                Some(self.lookup_in_chunk(state.chunk_index, state.lookup_index))
            } else {
                None
            }

        // String was not interned, or was already removed.
        } else {
            None
        }
    }

    /// Looks up a previously [`intern`]'ed string via its [`StringID`].
    ///
    /// Returns `None` if `string_id` does not correspond to a currently interned string.
    ///
    /// For use in multithreaded scenarios, in conjunction with `Mutex` / `RwLock`.
    ///
    /// [`intern`]: #method.intern
    /// [`StringID`]: struct.StringID.html
    pub unsafe fn lookup_unsafe(&self, string_id: StringID) -> Option<UnsafeStr> {
        self.lookup(string_id)
            .map(|string| UnsafeStr::from_str(string))
    }

    /// Internally decrements the ref count associated with the [`string_id`] of a previously [`intern`]'ed string.
    ///
    /// When the ref count reaches zero, the string is removed from the pool - it may no longer be [`looked up`].
    /// May invalidate the previously [`looked up`] strings.
    ///
    /// Does nothing if [`string_id`] does not correspond to a currently interned string.
    ///
    /// [`intern`]: #method.intern
    /// [`string_id`]: struct.StringID.html
    /// [`looked up`]: #method.lookup
    pub fn remove(&mut self, string_id: StringID) {
        let mut remove = false;

        // String was interned.
        if let Some(state) = self.lookup.get_mut(&string_id) {
            state.ref_count -= 1;

            // This was the last use of this string - remove it from the chunk.
            if state.ref_count == 0 {
                remove = true;

                StringPool::remove_from_chunk(
                    state.chunk_index,
                    state.lookup_index,
                    &mut self.chunks,
                    &mut self.lookup,
                );
            }
        }

        if remove {
            self.lookup.remove(&string_id);
        }
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
    pub fn remove_gc(&mut self, string_id: StringID) {
        // String was interned.
        if let Some(state) = self.lookup.get_mut(&string_id) {
            state.ref_count -= 1;

            self.gc.push(string_id);
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

    fn lookup_in_chunk(&self, chunk_index: u16, lookup_index: u16) -> &str {
        self.chunks[chunk_index as usize].lookup(lookup_index)
    }

    fn remove_from_chunk(
        chunk_index: ChunkIndex,
        lookup_index: LookupIndex,
        chunks: &mut Vec<StringChunk>,
        lookup: &mut HashMap<StringID, StringState>,
    ) {
        match chunks[chunk_index as usize].remove(lookup_index) {
            // The chunk is completely empty - we just free it immediately.
            RemoveResult::ChunkFree => {
                let last_chunk_index = (chunks.len() - 1) as u16;

                let free_chunk = chunks.swap_remove(chunk_index as usize);
                std::mem::drop(free_chunk);

                // Patch the chunk indices if necessary.
                if last_chunk_index != chunk_index {
                    for state in lookup
                        .iter_mut()
                        .filter_map(|(_, v)| {
                            if v.chunk_index == last_chunk_index {
                                Some(v)
                            } else {
                                None
                            }
                        })
                        .collect::<Vec<&mut StringState>>()
                    {
                        state.chunk_index = chunk_index;
                    }
                }
            }

            _ => {}
        }
    }
}

type ChunkIndex = u16;
type LookupIndex = u16;

/// Interned string descriptor.
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

type StringOffset = u16;
type StringLength = u16;

#[derive(Clone, Copy)]
struct StringInChunk {
    // String start offset from `data` array start.
    offset: StringOffset,

    // String length in bytes.
    length: StringLength,
}

struct StringChunk {
    /// Size of `data` array in bytes.
    chunk_size: u16,

    /// Num of bytes in `data` array containing string bytes.
    occupied_bytes: u16,

    /// First free byte in the `data` array.
    first_free_byte: StringOffset,

    fragmented: bool,

    /// Lookup array for string offsets/lengths.
    offset_lookup: Vec<StringInChunk>,

    data: *mut u8,
}

impl Drop for StringChunk {
    fn drop(&mut self) {
        free(self.data, self.chunk_size as usize);
    }
}

enum InternResult {
    /// Not enought free space left in the chunk.
    NoSpace,

    /// Successfully interned the string.
    /// Contains the lookup index.
    Interned(LookupIndex),
}

enum RemoveResult {
    /// Chunk still has some strings in it.
    ChunkInUse,

    /// Chunk is completely empty and may be freed.
    ChunkFree,
}

impl StringChunk {
    fn new(chunk_size: u16) -> Self {
        Self {
            chunk_size,
            occupied_bytes: 0,
            first_free_byte: 0,
            fragmented: true,
            offset_lookup: Vec::new(),

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

        let lookup_index = self.offset_lookup.len() as LookupIndex;
        self.offset_lookup.push(StringInChunk { offset, length });

        self.first_free_byte += length;

        // If we were defragmented and are now >50% occupancy -
        // mark the chunk as fragmented again.
        if !self.fragmented && ((self.occupied_bytes + length) > (self.chunk_size / 2)) {
            self.fragmented = true;
        }

        self.occupied_bytes += length;
        debug_assert!(self.occupied_bytes <= self.chunk_size);

        let src = string.as_bytes().as_ptr();
        let dst = unsafe { self.data.offset(offset as isize) };

        unsafe {
            std::ptr::copy_nonoverlapping(src, dst, length as usize);
        }

        InternResult::Interned(lookup_index)
    }

    fn lookup(&self, lookup_index: LookupIndex) -> &str {
        let string_in_chunk = &self.offset_lookup[lookup_index as usize];
        debug_assert!(string_in_chunk.offset < self.chunk_size);
        debug_assert!(string_in_chunk.length <= self.chunk_size);

        let slice = unsafe {
            let src = self.data.offset(string_in_chunk.offset as isize);
            std::slice::from_raw_parts(src, string_in_chunk.length as usize)
        };

        std::str::from_utf8(slice).unwrap()
    }

    fn remove(&mut self, lookup_index: LookupIndex) -> RemoveResult {
        let string_in_chunk = &mut self.offset_lookup[lookup_index as usize];
        debug_assert!(string_in_chunk.offset < self.chunk_size);
        debug_assert!(string_in_chunk.length <= self.chunk_size);
        debug_assert!(self.occupied_bytes >= string_in_chunk.length);

        unsafe {
            let dst = self.data.offset(string_in_chunk.offset as isize);

            // Invalid UTF-8 byte sequence.
            std::ptr::write_bytes(dst, b'\xc0', string_in_chunk.length as usize);
        }

        self.occupied_bytes -= string_in_chunk.length;

        string_in_chunk.offset = std::u16::MAX;
        string_in_chunk.length = std::u16::MAX;

        if self.occupied_bytes == 0 {
            return RemoveResult::ChunkFree;
        }

        // Defragment if <50% occupied and not already defragmented.
        if self.fragmented && (self.occupied_bytes < self.chunk_size / 2) {
            // Gather string ranges.
            let mut current_strings = Vec::new();

            for string_in_chunk in self.offset_lookup.iter() {
                if string_in_chunk.offset == std::u16::MAX {
                    debug_assert!(string_in_chunk.length == std::u16::MAX);
                    continue;
                }

                current_strings.push((*string_in_chunk, 0));
            }
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
                    .offset_lookup
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
        const CHUNK_SIZE: u16 = 8;

        let mut pool = StringPool::new(CHUNK_SIZE);

        let empty = "";

        let empty_id = pool.intern(empty);
        assert_eq!(empty_id, StringID::default());
        assert!(pool.lookup(empty_id).is_none());

        let asdf = "asdf";
        let gh = "gh";

        let asdf_id = pool.intern(asdf);
        assert_eq!(asdf_id.0, string_hash(asdf));
        assert_eq!(asdf_id, StringPool::string_id(asdf));

        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        // Should not allocate new data.
        let asdf_id_2 = pool.intern(asdf);
        assert_eq!(asdf_id, asdf_id_2);

        assert_eq!(pool.lookup(asdf_id_2).unwrap(), asdf);

        // This decrements the ref count.
        pool.remove(asdf_id_2);

        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        let gh_id = StringPool::string_id(gh);
        assert_eq!(gh_id.0, string_hash(gh));

        unsafe {
            pool.intern_with_id(gh, gh_id);
        }

        assert_eq!(pool.lookup(gh_id).unwrap(), gh);

        assert!(gh_id != asdf_id);

        let asdf_unsafe = unsafe { pool.lookup_unsafe(asdf_id).unwrap() };

        unsafe {
            assert_eq!(asdf_unsafe.to_str(), asdf);
        }

        // Should not trigger defragmentation.
        pool.remove_gc(asdf_id);

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

        // Should allocate a new chunk.
        let long_string = "asdfghjk";

        let long_string_id = pool.intern(long_string);

        assert_eq!(pool.lookup(long_string_id).unwrap(), long_string);

        // Should free the first chunk.
        pool.remove(gh_id);

        assert!(pool.lookup(gh_id).is_none());

        assert_eq!(pool.lookup(long_string_id).unwrap(), long_string);

        // Should free the last chunk.
        pool.remove(long_string_id);
    }
}
