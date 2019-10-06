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

use std::collections::{HashMap, hash_map::DefaultHasher};
use std::hash::{Hash, Hasher};

/// Unique interned string identifier.
/// Internally it's just a string hash (as provided by [`DefaultHasher`]) -
/// so `StringID` equality does not guarantee string equality.
///
/// [`DefaultHasher`]: https://doc.rust-lang.org/nightly/std/collections/hash_map/struct.DefaultHasher.html
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct StringID(pub u64);

/// Manages the collection of unique interned strings.
/// Uses ref-counting internally to deduplicate stored strings.
pub struct StringPool {
    chunk_size: u16,
    lookup: HashMap<StringID, StringState>,
    chunks: Vec<StringChunk>,
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
        }
    }

    /// Interns the string, returning the [`StringID`] which may be used to look it up or remove it from the pool.
    /// If `string` was laready interned, returns the same [`StringID`] as the one returned by the previous call to `intern`,
    /// internally incrementing the string's ref count.
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
            "Max supported interned string length in bytes is `{}` - tried to intern `{}` bytes.", self.chunk_size, string.len()
        );

        let string_id = StringID(string_hash(string));

        // String was already interned.
        if let Some(state) = self.lookup.get_mut(&string_id) {
            state.ref_count += 1;

            // Debug-only hash collision detection j ust a panic.
            // TODO - fix this.
            debug_assert_eq!(
                string,
                self.lookup(string_id).unwrap(),
                "Hash collision detected. Interned: \"{}\", new: \"{}\", hash: [{}].",
                self.lookup(string_id).unwrap(),
                string,
                string_id.0
            );

            return string_id;

        // Else the string has not been interned yet.
        } else {
            // Try to intern in all chunks in order.
            for (chunk_index, chunk) in self.chunks.iter_mut().enumerate() {
                match chunk.intern(string) {
                    InternResult::Interned(lookup_index) => {
                        let new_state = StringState::new(chunk_index as u16, lookup_index);
                        self.lookup.insert(string_id, new_state);

                        return string_id;
                    },
                    _ => {},
                }
            }

            // No chunks / no space in all chunks - allocate a new one.
            let mut chunk = StringChunk::new(self.chunk_size);
            let chunk_index = self.chunks.len();

            // Must succeed.
            let string_id = match chunk.intern(string) {
                InternResult::Interned(lookup_index) => {
                    let new_state = StringState::new(chunk_index as u16, lookup_index);
                    self.lookup.insert(string_id, new_state);

                    string_id
                },
                _ => { unreachable!() },
            };

            self.chunks.push(chunk);

            string_id
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
            return Some(self.lookup_in_chunk(state.chunk_index, state.lookup_index))

        // String was not interned, or was already removed.
        } else {
            None
        }
    }

    /// Internally decrements the ref count associated with the [`StringID`] of a previously [`intern`]'ed string.
    /// When the ref count reaches zero, the string is removed from the pool.
    ///
    /// Does nothing if `string_id` does not correspond to a currently interned string.
    ///
    /// [`intern`]: #method.intern
    /// [`StringID`]: struct.StringID.html
    pub fn remove(&mut self, string_id: StringID) {
        let mut remove = false;

        // String was interned.
        if let Some(state) = self.lookup.get_mut(&string_id) {
            state.ref_count -= 1;

            // This was the last use of this string - remove it from the chunk.
            if state.ref_count == 0 {
                remove = true;

                let chunk_index = state.chunk_index;

                match self.chunks[chunk_index as usize].remove(state.lookup_index) {
                    // The chunk is completely empty - we just free it immediately.
                    RemoveResult::ChunkFree => {
                        let last_chunk_index = (self.chunks.len() - 1) as u16;

                        let free_chunk = self.chunks.swap_remove(chunk_index as usize);
                        std::mem::drop(free_chunk);

                        // Patch the chunk indices if necessary.
                        if last_chunk_index != chunk_index {
                            for state in self.lookup.iter_mut().filter_map( |(_, v)| {
                                if v.chunk_index == last_chunk_index { Some(v) } else { None }
                            } ).collect::<Vec<&mut StringState>>() {
                                state.chunk_index = chunk_index;
                            }
                        }
                    },

                    _ => {},
                }
            }
        }

        if remove {
            self.lookup.remove(&string_id);
        }
    }

    fn lookup_in_chunk(&self, chunk_index: u16, lookup_index: u16) -> &str {
        self.chunks[chunk_index as usize].lookup(lookup_index)
    }
}

/// Interned string descriptor.
struct StringState {
    /// Ref count of the interned string.
    ref_count: u16,

    /// Index of the chunk in which the string is interned.
    chunk_index: u16,

    /// Index of the element in the chunk's offset lookup array
    /// which contains this string's offset from the chunk's start and its length.
    lookup_index: u16,
}

impl StringState {
    fn new(chunk_index: u16, lookup_index: u16) -> Self {
        Self {
            ref_count: 1,
            chunk_index,
            lookup_index,
        }
    }
}

#[derive(Clone, Copy)]
struct StringInChunk {
    // String start offset from `data` array start.
    offset: u16,

    // String length in bytes.
    length: u16,
}

struct StringChunk {
    /// Size of `data` array in bytes.
    chunk_size: u16,

    /// Num of bytes in `data` array containing string bytes.
    occupied_bytes: u16,

    /// First free byte in the `data` array.
    first_free_byte: u16,

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
    Interned(u16),
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
        let length = string.len() as u16;

        let remaining_bytes = self.chunk_size - self.first_free_byte;

        // Not enough space.
        if length > remaining_bytes {
            return InternResult::NoSpace;
        }

        let offset = self.first_free_byte;

        let lookup_index = self.offset_lookup.len() as u16;
        self.offset_lookup.push(StringInChunk {
            offset,
            length,
        });

        self.first_free_byte += length;

        // If we were defragmented and are now >50% occupancy -
        // mark the chunk as fragmented again.
        if !self.fragmented && ((self.occupied_bytes + length) > (self.chunk_size / 2)) {
            self.fragmented = true;
        }

        self.occupied_bytes += length;
        debug_assert!(self.occupied_bytes <= self.chunk_size);

        let src = string.as_bytes().as_ptr();
        let dst = unsafe {
            self.data.offset(offset as isize)
        };

        unsafe {
            std::ptr::copy_nonoverlapping(src, dst, length as usize);
        }

        InternResult::Interned(lookup_index)
    }

    fn lookup(&self, lookup_index: u16) -> &str {
        let string_in_chunk = &self.offset_lookup[lookup_index as usize];
        debug_assert!(string_in_chunk.offset < self.chunk_size);
        debug_assert!(string_in_chunk.length <= self.chunk_size);

        let slice = unsafe {
            let src = self.data.offset(string_in_chunk.offset as isize);
            std::slice::from_raw_parts(src, string_in_chunk.length as usize)
        };

        std::str::from_utf8(slice).unwrap()
    }

    fn remove(&mut self, lookup_index: u16) -> RemoveResult {
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

                current_strings.push((*string_in_chunk, 0u16));
            }
            debug_assert_eq!(current_strings.iter().fold(0, |sum, el| { sum + el.0.length }), self.occupied_bytes);

            // Sort by offset.
            current_strings.sort_by(|l, r| l.0.offset.cmp(&r.0.offset));

            // Compact.
            let mut offset = 0;

            for (string_in_chunk, new_offset) in current_strings.iter_mut() {
                unsafe {
                    let src = self.data.offset(string_in_chunk.offset as isize);
                    let dst = self.data.offset(offset as isize);

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
                let found = self.offset_lookup.iter_mut().find(|el| el.offset == string_in_chunk.offset).unwrap();
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
    let vec = unsafe {
        Vec::from_raw_parts(ptr, size, size)
    };
    std::mem::drop(vec);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        const CHUNK_SIZE: u16 = 8;

        let mut pool = StringPool::new(CHUNK_SIZE);

        let asdf = "asdf";
        let gh = "gh";

        let asdf_id = pool.intern(asdf);
        assert_eq!(asdf_id.0, string_hash(asdf));

        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        // Should not allocate new data.
        let asdf_id_2 = pool.intern(asdf);
        assert_eq!(asdf_id, asdf_id_2);

        assert_eq!(pool.lookup(asdf_id_2).unwrap(), asdf);

        // This decrements the ref count.
        pool.remove(asdf_id_2);

        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        let gh_id = pool.intern(gh);
        assert_eq!(gh_id.0, string_hash(gh));

        assert_eq!(pool.lookup(gh_id).unwrap(), gh);

        assert!(gh_id != asdf_id);

        // Should trigger defragmentation.
        pool.remove(asdf_id);

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
