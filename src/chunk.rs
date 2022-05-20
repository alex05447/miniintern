use std::{mem, num::NonZeroU16, ptr::NonNull};

/// Type for the size in bytes of the string chunks the [`Pool`](crate::Pool) allocates internally for string storage.
///
/// NOTE - currently, maximum chunk size is `std::u16::MAX`, which (minus the (small) string chunk header overhead)
/// determines the maximum length in bytes of the string which can be interned in the chunk by the [`string pool`].
/// Strings longer than this are allocated on the heap individually.
///
/// NOTE - when changing the underlying type, also change the `StringOffset` / `StringLength` / `LookupIndex` types.
pub type ChunkSize = NonZeroU16;

pub(crate) type ChunkSizeInternal = u16;

/// Type for the index of the string in the string chunk's `lookup` array.
///
/// NOTE - make sure the underlying type matches the `ChunkSize` type above.
pub(crate) type LookupIndex = u16;

/// Type for string offset within the string chunk's buffer.
///
/// NOTE - make sure the underlying type matches the `ChunkSize` type above.
pub(crate) type Offset = u16;

/// Used to indicate an invalid value for the string chunk free linked list index.
const INVALID_INDEX: Offset = Offset::MAX;

/// Type for string length within the string chunk buffer.
///
/// NOTE - make sure the underlying type matches the `ChunkSize` type above.
type Length = u16;

/// NOTE - we do not allow interning empty strings (and we do allow `std::u16::MAX` long strings),
/// so we can use `0` as a special value which means an unoccupied string chunk entry.
const INVALID_LENGTH: Length = 0;

/// Invalid UTF-8 byte sequence, used to fill the unused space in the string chunks in debug configuration.
const CHUNK_FILL_VALUE: u8 = b'\xc0';

pub(crate) const STRING_CHUNK_HEADER_SIZE: ChunkSizeInternal = mem::size_of::<Chunk>() as _;

/// Returned by `Chunk::intern`.
pub(crate) enum InternResult {
    /// Did not intern - not enough free space left in the chunk.
    /// NOTE - this is never returned because the string was too large for our chunk size,
    /// as we handle that case beforehand.
    NoSpace,
    /// Successfully interned the string.
    /// Contains the index of the string in the chunk's lookup array.
    Interned(LookupIndex),
}

/// Returned by `Chunk::remove`.
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
    offset: Offset,
    /// (Non-null) string length in bytes,
    /// or `INVALID_LENGTH` if used as the lookup array entry free list node.
    length: Length,
}

/// A fixed-size memory chunk used to store interned strings.
/// This struct is the chunk's header and is located at the start of its data buffer,
/// taking up dome space.
pub(crate) struct Chunk {
    /// The chunk's string data buffer.
    /// Points past the chunk's header.
    /// The string pool knows its size and passes it down when necessary.
    data: *mut u8,
    /// Num of bytes in `data` array containing string bytes.
    occupied_bytes: ChunkSizeInternal,
    /// First free byte in the `data` array.
    first_free_byte: Offset,
    /// Starts `false`.
    /// Set to `true` when interning, whenever occupancy reaches >50%.
    /// Set to `false` when removing, whenever occupancy reaches <50% and the chunk is defragmented.
    fragmented: bool,
    /// Lookup array which maps the string's stable `StringState::lookup_index` to its offset/length within the chunk's data buffer.
    lookup: Vec<StringInChunk>,
    /// First free index in the lookup array, or `INVALID_INDEX`.
    /// Free lookup array entries form a linked list via their `offset` field.
    first_free_index: Offset,
}

impl Chunk {
    /// Allocates a new `Chunk` on the heap.
    pub(crate) fn allocate(chunk_size: ChunkSizeInternal) -> NonNull<Self> {
        // Ensured by the caller.
        debug_assert!(chunk_size > STRING_CHUNK_HEADER_SIZE);

        // Allocate the chunk's data buffer.
        // Fill it with UTF-8 garbage in debug configuration.
        let ptr = malloc(
            chunk_size as _,
            if cfg!(debug_assertions) {
                CHUNK_FILL_VALUE
            } else {
                0
            },
        )
        .as_ptr();

        // Create the chunk's header, passing it the offset data buffer pointer,
        // and write the header at the start of the buffer.

        let data = unsafe { ptr.offset(STRING_CHUNK_HEADER_SIZE as _) };

        let chunk = Self::new(data);

        unsafe { std::ptr::write_unaligned(ptr as _, chunk) };

        unsafe { NonNull::new_unchecked(ptr as _) }
    }

    /// Cleans up and frees the `Chunk`.
    pub(crate) fn free(ptr: NonNull<Chunk>, chunk_size: ChunkSizeInternal) {
        let chunk = unsafe { std::ptr::read_unaligned(ptr.as_ptr()) };
        mem::drop(chunk);

        free(
            unsafe { NonNull::new_unchecked(ptr.as_ptr() as _) },
            chunk_size as _,
        );
    }

    /// Tries to intern the `string` in this chunk.
    /// `data_size` is the maximum useful size in bytes of the string chunk's buffer (i.e. excluding the header).
    ///
    /// Caller guarantees `string` fits in `data_size`.
    pub(crate) fn intern(&mut self, string: &str, data_size: ChunkSizeInternal) -> InternResult {
        let length = string.len() as Length;
        debug_assert!(length <= data_size);

        debug_assert!(data_size >= self.first_free_byte);
        let remaining_bytes = data_size - self.first_free_byte;

        // Not enough space.
        if length > remaining_bytes {
            return InternResult::NoSpace;
        }

        let offset = self.first_free_byte;

        // Get the lookup index from the free list, or allocate a new element.
        let lookup_index = if self.first_free_index != INVALID_INDEX {
            let lookup_index = self.first_free_index;
            debug_assert!((lookup_index as usize) < self.lookup.len());
            let string_in_chunk = unsafe { self.lookup.get_unchecked_mut(lookup_index as usize) };
            debug_assert_eq!(string_in_chunk.length, INVALID_LENGTH);
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
        debug_assert!(self.occupied_bytes <= data_size);

        // If we were defragmented and are now >50% occupancy -
        // mark the chunk as fragmented.
        if !self.fragmented && (self.occupied_bytes > (data_size / 2)) {
            self.fragmented = true;
        }

        // COpy the string's data into the allocated space in the chunk.
        let src = string.as_bytes().as_ptr();
        let dst = unsafe { self.data.offset(offset as _) };

        unsafe {
            std::ptr::copy_nonoverlapping(src, dst, length as _);
        }

        InternResult::Interned(lookup_index)
    }

    /// Looks up the string in this chunk given its `lookup_index`.
    ///
    /// `data_size` is the maximum useful size in bytes of the string chunk's buffer (i.e. excluding the header),
    /// only used for a debug bounds check.
    ///
    /// NOTE - the caller guarantees `lookup_index` is valid, so the call always succeeds.
    pub(crate) fn lookup(&self, lookup_index: LookupIndex, data_size: ChunkSizeInternal) -> &str {
        // Lookup the string's offset/lenght in the chunk using its stable `lookup_index`.
        let lookup_index = lookup_index as usize;
        debug_assert!(lookup_index < self.lookup.len());
        let string_in_chunk = unsafe { self.lookup.get_unchecked(lookup_index) };

        debug_assert!(
            (string_in_chunk.offset + string_in_chunk.length) <= data_size,
            "string in chunk is out of bounds"
        );

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
    /// Also defragments the string chunk if it was fragmented and this causes its occupancy to drop below 50%.
    ///
    /// `data_size` is the maximum useful size in bytes of the string chunk's buffer (i.e. excluding the header),
    ///
    /// NOTE - the caller guarantees `lookup_index` is valid, so the call always succeeds.
    pub(crate) fn remove(
        &mut self,
        index: LookupIndex,
        data_size: ChunkSizeInternal,
        offsets: &mut Vec<(StringInChunk, Offset)>,
    ) -> RemoveResult {
        debug_assert!((index as usize) < self.lookup.len());
        let string_in_chunk = unsafe { self.lookup.get_unchecked_mut(index as usize) };
        debug_assert!((string_in_chunk.offset + string_in_chunk.length) <= data_size);

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
        self.first_free_index = index;

        // Defragment if <50% occupied and not already defragmented.
        if self.needs_to_defragment(data_size) {
            self.defragment(data_size, offsets);
        }

        RemoveResult::ChunkInUse
    }

    fn new(data: *mut u8) -> Self {
        Self {
            data,
            occupied_bytes: 0,
            first_free_byte: 0,
            fragmented: false,
            lookup: Vec::new(),
            first_free_index: INVALID_INDEX,
        }
    }

    fn needs_to_defragment(&self, data_size: ChunkSizeInternal) -> bool {
        self.fragmented && (self.occupied_bytes < data_size / 2)
    }

    #[cold]
    fn defragment(
        &mut self,
        data_size: ChunkSizeInternal,
        offsets: &mut Vec<(StringInChunk, Offset)>,
    ) {
        debug_assert!(self.fragmented);

        // Gather the string ranges.
        // Tuples of (current string offset/length, new string offset).
        debug_assert!(offsets.is_empty());
        offsets.extend(self.lookup.iter().filter_map(|string_in_chunk| {
            // Skip the free entries.
            (string_in_chunk.length != INVALID_LENGTH).then(|| (*string_in_chunk, 0))
        }));

        // Sanity check - string lengths must add up to chunk's occupied bytes.
        debug_assert_eq!(
            offsets.iter().map(|(el, _)| el.length).sum::<u16>(),
            self.occupied_bytes
        );

        // Sort by current offset.
        offsets.sort_by(|l, r| l.0.offset.cmp(&r.0.offset));

        // Compact.
        let mut offset = 0;

        for (string_in_chunk, new_offset) in offsets.iter_mut() {
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
            let remaining_bytes = data_size - self.first_free_byte;

            if remaining_bytes > 0 {
                unsafe {
                    let dst = self.data.offset(self.first_free_byte as isize);
                    std::ptr::write_bytes(dst, CHUNK_FILL_VALUE, remaining_bytes as usize);
                }
            }
        }

        // Patch the string offsets.
        for (new_string, new_offset) in offsets.iter() {
            // NOTE - always succeeds.
            if let Some(found) = self
                .lookup
                .iter_mut()
                .find(|old_string| old_string.offset == new_string.offset)
            {
                found.offset = *new_offset;
            }
        }

        offsets.clear();

        self.fragmented = false;
    }
}

fn malloc(size: usize, val: u8) -> NonNull<u8> {
    let mut vec = vec![val; size];
    let ptr = vec.as_mut_ptr();
    mem::forget(vec);
    NonNull::new(ptr).expect("out of memory")
}

fn free(ptr: NonNull<u8>, size: usize) {
    let vec = unsafe { Vec::from_raw_parts(ptr.as_ptr(), size, size) };
    mem::drop(vec);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string_chunk() {
        const SMALL_CHUNK_DATA_SIZE: ChunkSizeInternal = 8;
        assert!(SMALL_CHUNK_DATA_SIZE < STRING_CHUNK_HEADER_SIZE);
        const SMALL_CHUNK_SIZE: ChunkSizeInternal =
            SMALL_CHUNK_DATA_SIZE + STRING_CHUNK_HEADER_SIZE;

        let mut chunk = Chunk::allocate(SMALL_CHUNK_SIZE);

        let chunk_ref = unsafe { chunk.as_mut() };

        assert_eq!(chunk_ref.occupied_bytes, 0);
        assert_eq!(chunk_ref.first_free_byte, 0);
        assert!(!chunk_ref.fragmented);
        assert!(chunk_ref.lookup.is_empty());
        assert_eq!(chunk_ref.first_free_index, INVALID_INDEX);

        let foo_idx =
            if let InternResult::Interned(idx) = chunk_ref.intern("foo", SMALL_CHUNK_DATA_SIZE) {
                idx
            } else {
                panic!("failed to intern");
            };

        assert_eq!(foo_idx, 0);

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

        assert_eq!(chunk_ref.lookup(foo_idx, SMALL_CHUNK_DATA_SIZE), "foo");

        let bar_idx =
            if let InternResult::Interned(idx) = chunk_ref.intern("bar", SMALL_CHUNK_DATA_SIZE) {
                idx
            } else {
                panic!("failed to intern");
            };

        assert_eq!(bar_idx, 1);

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

        assert_eq!(chunk_ref.lookup(bar_idx, SMALL_CHUNK_DATA_SIZE), "bar");

        assert!(matches!(
            chunk_ref.intern("baz", SMALL_CHUNK_DATA_SIZE),
            InternResult::NoSpace
        ));

        let mut string_offsets = Vec::new();

        assert!(matches!(
            chunk_ref.remove(foo_idx, SMALL_CHUNK_DATA_SIZE, &mut string_offsets),
            RemoveResult::ChunkInUse
        ));

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

        let baz_idx =
            if let InternResult::Interned(idx) = chunk_ref.intern("baz", SMALL_CHUNK_DATA_SIZE) {
                idx
            } else {
                panic!("failed to intern");
            };

        assert_eq!(baz_idx, 0);

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

        assert_eq!(chunk_ref.lookup(baz_idx, SMALL_CHUNK_DATA_SIZE), "baz");

        assert!(matches!(
            chunk_ref.remove(bar_idx, SMALL_CHUNK_DATA_SIZE, &mut string_offsets),
            RemoveResult::ChunkInUse
        ));

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

        assert!(matches!(
            chunk_ref.remove(baz_idx, SMALL_CHUNK_DATA_SIZE, &mut string_offsets),
            RemoveResult::ChunkFree
        ));

        Chunk::free(chunk, SMALL_CHUNK_SIZE);

        const LARGE_CHUNK_SIZE: ChunkSizeInternal = 256;
        assert!(LARGE_CHUNK_SIZE > STRING_CHUNK_HEADER_SIZE);

        const LARGE_CHUNK_DATA_SIZE: ChunkSizeInternal =
            LARGE_CHUNK_SIZE - STRING_CHUNK_HEADER_SIZE;

        let mut chunk = Chunk::allocate(LARGE_CHUNK_SIZE);

        let chunk_ref = unsafe { chunk.as_mut() };

        assert_eq!(chunk_ref.occupied_bytes, 0);
        assert_eq!(chunk_ref.first_free_byte, 0);
        assert!(!chunk_ref.fragmented);
        assert!(chunk_ref.lookup.is_empty());
        assert_eq!(chunk_ref.first_free_index, INVALID_INDEX);

        let large_string_idx = if let InternResult::Interned(idx) =
            chunk_ref.intern("asdfghjkl", LARGE_CHUNK_DATA_SIZE)
        {
            idx
        } else {
            panic!("failed to intern");
        };

        assert_eq!(large_string_idx, 0);

        assert_eq!(chunk_ref.occupied_bytes, 9);
        assert_eq!(chunk_ref.first_free_byte, 9);
        assert!(!chunk_ref.fragmented);
        assert_eq!(
            &chunk_ref.lookup[..],
            &[StringInChunk {
                offset: 0,
                length: 9
            }]
        );
        assert_eq!(chunk_ref.first_free_index, INVALID_INDEX);

        assert_eq!(
            chunk_ref.lookup(foo_idx, LARGE_CHUNK_DATA_SIZE),
            "asdfghjkl"
        );

        assert!(matches!(
            chunk_ref.remove(large_string_idx, LARGE_CHUNK_DATA_SIZE, &mut string_offsets),
            RemoveResult::ChunkFree
        ));

        Chunk::free(chunk, LARGE_CHUNK_SIZE);
    }
}
