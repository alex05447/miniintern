use std::ptr::NonNull;

/// Type for the size in bytes of the string chunks the [`string pool`] allocates internally for string storage.
///
/// NOTE - currently, maximum chunk size is `std::u16::MAX`, which (minus the (small) string chunk header overhead)
/// determines the maximum length in bytes of the string which can be interned by the [`string pool`].
///
/// NOTE - when changing the underlying type, also change the `StringOffset` / `StringLength` / `LookupIndex` types.
///
/// [`string pool`]: struct.StringPool.html
pub type ChunkSize = u16;

/// Type for the index of the string in the string chunk's `lookup` array.
///
/// NOTE - make sure the underlying type matches the `ChunkSize` type above.
pub(crate) type LookupIndex = u16;

/// Type for string offset within the string chunk's buffer.
///
/// NOTE - make sure the underlying type matches the `ChunkSize` type above.
type StringOffset = u16;

/// Used to indicate an invalid value for the string chunk free linked list index.
const INVALID_INDEX: StringOffset = StringOffset::MAX;

/// Type for string length within the string chunk buffer.
///
/// NOTE - make sure the underlying type matches the `ChunkSize` type above.
type StringLength = u16;

/// NOTE - we do not allow interning empty strings (and we do allow `std::u16::MAX` long strings),
/// so we can use `0` as a special value which means an unoccupied string chunk entry.
const INVALID_LENGTH: u16 = 0;

/// Invalid UTF-8 byte sequence, used to fill the unused space in the string chunks.
//#[cfg(debug)]
const CHUNK_FILL_VALUE: u8 = b'\xc0';

pub(crate) const STRING_CHUNK_HEADER_SIZE: u16 = std::mem::size_of::<StringChunk>() as u16;

pub(crate) enum InternResult {
    /// Not enough free space left in the chunk.
    NoSpace,
    /// Successfully interned the string.
    /// Contains the index of the string in the chunk's lookup array.
    Interned(LookupIndex),
}

pub(crate) enum RemoveResult {
    /// Chunk still has some strings in it.
    ChunkInUse,
    /// Chunk is completely empty and may be freed.
    ChunkFree,
}

/// Describes the interned string slice's location in the string chunk.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct StringInChunk {
    /// String start offset in bytes from `data` array start.
    /// Also used as the lookup array entry free list node, or `INVALID_INDEX`.
    offset: StringOffset,
    /// (non-null) string length in bytes.
    length: StringLength,
}

/// A fixed-size memory chunk used to store interned strings.
pub(crate) struct StringChunk {
    /// The chunk's string data buffer.
    data: *mut u8,
    /// Size of `data` array in bytes.
    /// Needed for `free`, `intern`, `lookup`, `remove`.
    /// TODO: remove this.
    data_size: ChunkSize,
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
    /// Scratch pad vec used for defragmenting.
    /// Persisted to avoid allocating a new one in each call to `defragment()`.
    /// TODO: investigate if it's worth it.
    string_offsets: Vec<(StringInChunk, StringOffset)>,
}

impl StringChunk {
    /// Allocates a new `StringChunk` on the heap.
    pub(crate) fn allocate(chunk_size: ChunkSize) -> NonNull<Self> {
        // Ensured by the caller.
        debug_assert!(chunk_size > STRING_CHUNK_HEADER_SIZE);

        let data_size = chunk_size - STRING_CHUNK_HEADER_SIZE;

        let ptr = malloc(
            chunk_size as _,
            if cfg!(debug_assertions) {
                CHUNK_FILL_VALUE
            } else {
                0
            },
        )
        .as_ptr();

        let data = unsafe { ptr.offset(STRING_CHUNK_HEADER_SIZE as _) };

        let chunk = Self::new(data, data_size);

        unsafe { std::ptr::write_unaligned(ptr as _, chunk) };

        unsafe { NonNull::new_unchecked(ptr as _) }
    }

    /// Cleans up and frees the `StringChunk`.
    pub(crate) fn free(ptr: NonNull<StringChunk>) {
        let chunk = unsafe { std::ptr::read_unaligned(ptr.as_ptr()) };
        let data_size = chunk.data_size;
        std::mem::drop(chunk);

        let chunk_size = data_size + STRING_CHUNK_HEADER_SIZE;

        free(
            unsafe { NonNull::new_unchecked(ptr.as_ptr() as _) },
            chunk_size as _,
        );
    }

    /// Tries to intern the string in this chunk.
    pub(crate) fn intern(&mut self, string: &str) -> InternResult {
        let length = string.len();
        // NOTE - guaranteed to fit by the calling code.
        debug_assert!(length <= self.data_size as usize);
        let length = length as StringLength;

        debug_assert!(self.data_size >= self.first_free_byte);
        let remaining_bytes = self.data_size - self.first_free_byte;

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
            debug_assert_eq!(string_in_chunk.length, INVALID_LENGTH);
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
        debug_assert!(self.occupied_bytes <= self.data_size);

        // If we were defragmented and are now >50% occupancy -
        // mark the chunk as fragmented.
        if !self.fragmented && (self.occupied_bytes > (self.data_size / 2)) {
            self.fragmented = true;
        }

        let src = string.as_bytes().as_ptr();
        let dst = unsafe { self.data.offset(offset as _) };

        unsafe {
            std::ptr::copy_nonoverlapping(src, dst, length as _);
        }

        InternResult::Interned(lookup_index)
    }

    /// Looks up the string in this chunk given its `lookup_index`.
    /// NOTE - the caller guarantees `lookup_index` is valid, so the call always succeeds.
    pub(crate) fn lookup(&self, lookup_index: LookupIndex) -> &str {
        let lookup_index = lookup_index as usize;
        debug_assert!(lookup_index < self.lookup.len());
        let string_in_chunk = unsafe { self.lookup.get_unchecked(lookup_index) };
        debug_assert!(string_in_chunk.offset < self.data_size);
        debug_assert!(string_in_chunk.length <= self.data_size);

        unsafe {
            let src = self.data.offset(string_in_chunk.offset as isize);
            let slice = std::slice::from_raw_parts(src, string_in_chunk.length as usize);
            if cfg!(debug_assertions) {
                std::str::from_utf8(slice).unwrap()
            } else {
                std::str::from_utf8_unchecked(slice)
            }
        }
    }

    /// Removes the string from this chunk given its `lookup_index`.
    /// NOTE - the caller guarantees `lookup_index` is valid, so the call always succeeds.
    pub(crate) fn remove(&mut self, lookup_index: LookupIndex) -> RemoveResult {
        debug_assert!((lookup_index as usize) < self.lookup.len());
        let string_in_chunk = unsafe { self.lookup.get_unchecked_mut(lookup_index as usize) };
        debug_assert!(string_in_chunk.offset < self.data_size);
        debug_assert!(string_in_chunk.length <= self.data_size);

        // Fill the now empty space with garbage.
        if cfg!(debug_assertions) {
            unsafe {
                let dst = self.data.offset(string_in_chunk.offset as _);
                std::ptr::write_bytes(dst, CHUNK_FILL_VALUE, string_in_chunk.length as _);
            }
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
        if self.needs_to_defragment() {
            self.defragment();
        }

        RemoveResult::ChunkInUse
    }

    fn new(data: *mut u8, data_size: ChunkSize) -> Self {
        Self {
            data,
            data_size,
            occupied_bytes: 0,
            first_free_byte: 0,
            fragmented: false,
            lookup: Vec::new(),
            first_free_index: INVALID_INDEX,
            string_offsets: Vec::new(),
        }
    }

    fn needs_to_defragment(&self) -> bool {
        self.fragmented && (self.occupied_bytes < self.data_size / 2)
    }

    #[cold]
    fn defragment(&mut self) {
        debug_assert!(self.fragmented);

        // Gather the string ranges.
        // Tuples of (current string offset/length, new string offset).
        debug_assert!(self.string_offsets.is_empty());
        self.string_offsets
            .extend(self.lookup.iter().filter_map(|string_in_chunk| {
                // Skip the free entries.
                if string_in_chunk.length == INVALID_LENGTH {
                    None
                } else {
                    Some((*string_in_chunk, 0))
                }
            }));

        // Sanity check - string lengths must add up to chunk's occupied bytes.
        debug_assert_eq!(
            self.string_offsets
                .iter()
                .fold(0, |sum, el| { sum + el.0.length }),
            self.occupied_bytes
        );

        // Sort by current offset.
        self.string_offsets
            .sort_by(|l, r| l.0.offset.cmp(&r.0.offset));

        // Compact.
        let mut offset = 0;

        for (string_in_chunk, new_offset) in self.string_offsets.iter_mut() {
            unsafe {
                let src = self.data.offset(string_in_chunk.offset as _);
                let dst = self.data.offset(offset as _);

                // May overlap.
                std::ptr::copy(src, dst, string_in_chunk.length as _);

                *new_offset = offset;
                offset += string_in_chunk.length;
            }
        }
        debug_assert_eq!(offset, self.occupied_bytes);

        // Move the free pointer back.
        self.first_free_byte = self.occupied_bytes;

        // Fill the now free space with garbage.
        if cfg!(debug_assertions) {
            let remaining_bytes = self.data_size - self.first_free_byte;

            if remaining_bytes > 0 {
                unsafe {
                    let dst = self.data.offset(self.first_free_byte as isize);

                    std::ptr::write_bytes(dst, CHUNK_FILL_VALUE, remaining_bytes as usize);
                }
            }
        }

        // Patch the string offsets.
        for (new_string, new_offset) in self.string_offsets.iter() {
            let found = self
                .lookup
                .iter_mut()
                .find(|old_string| old_string.offset == new_string.offset)
                .unwrap();
            found.offset = *new_offset;
        }

        self.string_offsets.clear();

        self.fragmented = false;
    }
}

fn malloc(size: usize, val: u8) -> NonNull<u8> {
    let mut vec = vec![val; size];
    let ptr = vec.as_mut_ptr();
    std::mem::forget(vec);
    NonNull::new(ptr).expect("out of memory")
}

fn free(ptr: NonNull<u8>, size: usize) {
    let vec = unsafe { Vec::from_raw_parts(ptr.as_ptr(), size, size) };
    std::mem::drop(vec);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string_chunk() {
        const SMALL_CHUNK_SIZE: ChunkSize = 8;
        assert!(SMALL_CHUNK_SIZE < STRING_CHUNK_HEADER_SIZE);

        let mut chunk = StringChunk::allocate(SMALL_CHUNK_SIZE + STRING_CHUNK_HEADER_SIZE);

        let chunk_ref = unsafe { chunk.as_mut() };

        assert_eq!(chunk_ref.data_size, SMALL_CHUNK_SIZE);
        assert_eq!(chunk_ref.occupied_bytes, 0);
        assert_eq!(chunk_ref.first_free_byte, 0);
        assert!(!chunk_ref.fragmented);
        assert!(chunk_ref.lookup.is_empty());
        assert_eq!(chunk_ref.first_free_index, INVALID_INDEX);

        let foo_idx = if let InternResult::Interned(idx) = chunk_ref.intern("foo") {
            idx
        } else {
            panic!("failed to intern");
        };

        assert_eq!(foo_idx, 0);

        assert_eq!(chunk_ref.data_size, SMALL_CHUNK_SIZE);
        assert_eq!(chunk_ref.occupied_bytes, 3);
        assert_eq!(chunk_ref.first_free_byte, 3);
        assert!(!chunk_ref.fragmented);
        assert_eq!(
            &chunk_ref.lookup[..],
            &[StringInChunk {
                offset: 0,
                length: 3
            }]
        );
        assert_eq!(chunk_ref.first_free_index, INVALID_INDEX);

        assert_eq!(chunk_ref.lookup(foo_idx), "foo");

        let bar_idx = if let InternResult::Interned(idx) = chunk_ref.intern("bar") {
            idx
        } else {
            panic!("failed to intern");
        };

        assert_eq!(bar_idx, 1);

        assert_eq!(chunk_ref.data_size, SMALL_CHUNK_SIZE);
        assert_eq!(chunk_ref.occupied_bytes, 6);
        assert_eq!(chunk_ref.first_free_byte, 6);
        assert!(chunk_ref.fragmented); // <- became fragmented as >50% occupancy
        assert_eq!(
            &chunk_ref.lookup[..],
            &[
                StringInChunk {
                    offset: 0,
                    length: 3
                },
                StringInChunk {
                    offset: 3,
                    length: 3
                }
            ]
        );
        assert_eq!(chunk_ref.first_free_index, INVALID_INDEX);

        assert_eq!(chunk_ref.lookup(bar_idx), "bar");

        assert!(matches!(chunk_ref.intern("baz"), InternResult::NoSpace));

        assert!(matches!(
            chunk_ref.remove(foo_idx),
            RemoveResult::ChunkInUse
        ));

        assert_eq!(chunk_ref.data_size, SMALL_CHUNK_SIZE);
        assert_eq!(chunk_ref.occupied_bytes, 3);
        assert_eq!(chunk_ref.first_free_byte, 3); // <- was defragmented as <50% occupancy
        assert!(!chunk_ref.fragmented); // <- was defragmented as <50% occupancy
        assert_eq!(
            &chunk_ref.lookup[..],
            &[
                StringInChunk {
                    offset: INVALID_INDEX,
                    length: INVALID_LENGTH
                },
                StringInChunk {
                    offset: 0,
                    length: 3
                }
            ]
        ); // <- has 1 hole
        assert_eq!(chunk_ref.first_free_index, 0);

        let baz_idx = if let InternResult::Interned(idx) = chunk_ref.intern("baz") {
            idx
        } else {
            panic!("failed to intern");
        };

        assert_eq!(baz_idx, 0);

        assert_eq!(chunk_ref.data_size, SMALL_CHUNK_SIZE);
        assert_eq!(chunk_ref.occupied_bytes, 6);
        assert_eq!(chunk_ref.first_free_byte, 6);
        assert!(chunk_ref.fragmented); // <- became fragmented as >50% occupancy
        assert_eq!(
            &chunk_ref.lookup[..],
            &[
                StringInChunk {
                    offset: 3,
                    length: 3
                },
                StringInChunk {
                    offset: 0,
                    length: 3
                }
            ]
        );
        assert_eq!(chunk_ref.first_free_index, INVALID_INDEX);

        assert_eq!(chunk_ref.lookup(baz_idx), "baz");

        assert!(matches!(
            chunk_ref.remove(bar_idx),
            RemoveResult::ChunkInUse
        ));

        assert_eq!(chunk_ref.data_size, SMALL_CHUNK_SIZE);
        assert_eq!(chunk_ref.occupied_bytes, 3);
        assert_eq!(chunk_ref.first_free_byte, 3); // <- was defragmented as <50% occupancy
        assert!(!chunk_ref.fragmented); // <- was defragmented as <50% occupancy
        assert_eq!(
            &chunk_ref.lookup[..],
            &[
                StringInChunk {
                    offset: 0,
                    length: 3
                },
                StringInChunk {
                    offset: INVALID_INDEX,
                    length: INVALID_LENGTH
                }
            ]
        ); // <- has 1 hole
        assert_eq!(chunk_ref.first_free_index, 1);

        assert!(matches!(chunk_ref.remove(baz_idx), RemoveResult::ChunkFree));

        StringChunk::free(chunk);

        const LARGE_CHUNK_SIZE: ChunkSize = 256;
        assert!(LARGE_CHUNK_SIZE > STRING_CHUNK_HEADER_SIZE);

        let mut chunk = StringChunk::allocate(LARGE_CHUNK_SIZE);

        let chunk_ref = unsafe { chunk.as_mut() };

        assert_eq!(
            chunk_ref.data_size,
            LARGE_CHUNK_SIZE - STRING_CHUNK_HEADER_SIZE
        );
        assert_eq!(chunk_ref.occupied_bytes, 0);
        assert_eq!(chunk_ref.first_free_byte, 0);
        assert!(!chunk_ref.fragmented);
        assert!(chunk_ref.lookup.is_empty());
        assert_eq!(chunk_ref.first_free_index, INVALID_INDEX);

        StringChunk::free(chunk);
    }
}
