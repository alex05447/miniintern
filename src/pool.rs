use {
    crate::*,
    minimultimap::*,
    miniunchecked::*,
    std::{borrow::Cow, iter::Iterator, ptr::NonNull},
};

/// Type for the ref count of interned strings.
///
/// Determines how many copies of a string may be interned before an overflow error.
///
/// NOTE - update the docs for `intern` / `copy` when changing this.
type RefCount = u32;

/// Storage info for an interned string stored in a chunk.
#[derive(Clone)]
struct ChunkString {
    /// Pointer to the string chunk the string is interned in.
    /// Strings never move between chunks.
    /// Pointer is always valid, string chunks have a longer lifetime than any `ChunkString` holding on to them.
    chunk: NonNull<Chunk>,
    /// Index of the element in the string chunk's `lookup` array,
    /// which contains this string's offset from the chunk's data buffer start and its length.
    index: LookupIndex,
}

impl ChunkString {
    fn string_chunk(&self) -> &Chunk {
        unsafe { self.chunk.as_ref() }
    }
}

/// Type of interned string storage (chunk or heap) and its state.
#[derive(Clone)]
enum Storage {
    /// Most strings are stored in chunks.
    /// Holds the pointer to the chunk.
    Chunk(ChunkString),
    /// Strings longer than chunk size are stored individually on the heap as a `String`.
    String(String),
}

/// Interned string info.
#[derive(Clone)]
struct State {
    /// Ref count of the interned string.
    ref_count: RefCount,
    /// Generation of the interned string.
    generation: Generation,
    /// The string's storage info - in the chunk or on the heap.
    storage: Storage,
}

impl State {
    /// Create a new string state for a string stored in the chunk at `lookup_index`.
    fn new_chunk(
        generation: Generation,
        string_chunk: NonNull<Chunk>,
        lookup_index: LookupIndex,
    ) -> Self {
        Self {
            ref_count: 1,
            generation,
            storage: Storage::Chunk(ChunkString {
                chunk: string_chunk,
                index: lookup_index,
            }),
        }
    }

    /// Create a new string state for a string stored on the heap as a `String`
    /// (if the string is too large to fit in our chunks).
    fn new_string(generation: Generation, string: String) -> Self {
        Self {
            ref_count: 1,
            generation,
            storage: Storage::String(string),
        }
    }

    /// Returns the string slice of this string state.
    ///
    /// `data_size` is the maximum useful size in bytes of the string chunk's buffer (i.e. excluding the header),
    /// only used for a debug bounds check.
    fn lookup(&self, data_size: ChunkSizeInternal) -> &str {
        match &self.storage {
            Storage::Chunk(chunk) => chunk.string_chunk().lookup(chunk.index, data_size),
            Storage::String(string) => string.as_str(),
        }
    }
}

/// A string slice in the [`string pool`] represented as a raw pointer + length.
/// Returned by [`lookup_unsafe`].
/// Used as an escape hatch for `MutexGuard<Pool>` / `RwLockGuard<Pool>` string lifetime.
///
/// [`lookup_unsafe`]: struct.Pool.html#method.lookup_unsafe
/// [`string pool`]: struct.Pool.html
pub struct UnsafeStr((*const u8, usize));

impl UnsafeStr {
    /// Returns the actual interned string slice.
    ///
    /// # Safety
    ///
    /// Unsafe because it's up to the user to ensure the string does not outlive the [`string pool`]
    /// or is not invalidated by a call to [`remove`].
    ///
    /// [`remove`]: struct.Pool.html#method.remove
    /// [`string pool`]: struct.Pool.html
    pub unsafe fn to_str(&self) -> &'static str {
        std::str::from_utf8_unchecked(std::slice::from_raw_parts((self.0).0, (self.0).1))
    }

    unsafe fn from_str(string: &str) -> Self {
        Self((string.as_ptr(), string.len()))
    }
}

type NumStrings = u32;
const MAX_NUM_STRINGS: NumStrings = NumStrings::MAX;

/// String pool / arena.
///
/// Manages a collection of unique interned strings and associates them with opaque unique [`identifiers`](ID).
/// Attempts to store the strings contiguosly in (configurable) fixed-size memory chunks, allocated on demand.
///
/// Uses ref-counting internally to deduplicate stored strings
/// and intermittent defragmentation on remove to compact used memory.
pub struct Pool {
    /// Size in bytes of string chunks, allocated by the string pool to store the strings.
    /// Determines (minus the string hunk header overhead) the max supported interned string length in bytes.
    chunk_size: ChunkSizeInternal,
    /// Maps the string hash to (one or multiple, in case of hash collisions) string states - ref count, generation and chunk / index in chunk.
    lookup: MultiMap<Hash, State>,
    /// Total number of unique strings interned in the pool
    /// (including not-yet-garbage-collected strings).
    num_strings: NumStrings,
    /// Current string generation monotonic counter, incremented for each interned unique string.
    /// Used to invalidate removed `ID`'s.
    generation: Generation,
    /// All chunks allocated by the string pool.
    chunks: Vec<NonNull<Chunk>>,
    /// Cached pointer to the last chunk a string was successfully interned in,
    /// used to slightly speed up the interning operation.
    last_used_chunk: Option<NonNull<Chunk>>,
    /// String ID's of all strings removed from the string pool via `remove_gc` (their ref count reached `0`),
    /// bot not yet garbage collected.
    gc: Vec<ID>,
    /// Scratch pad vec used for string chunk defragmenting.
    /// Persisted and reused to avoid allocating a new one in each call to `defragment`.
    offsets: Vec<(StringInChunk, Offset)>,
}

impl Pool {
    /// Creates a new [`Pool`].
    ///
    /// String pool will allocate memory in `chunk_size` byte chunks
    /// (unless `chunk_size` is smaller than the (small) string chunk header overhead,
    /// in which case slightly more memory will be allocated per chunk).
    ///
    /// `chunk_size` determines the max string length in bytes which may be interned in a chunk.
    /// Larger chunks allow for longer strings to be stored, but may have higher memory fragmentation
    /// if the strings are frequently added and removed, as the pool makes no effort to reuse
    /// free space in chunks until it exceeds 50% of the chunk's size.
    /// Strings longer than `chunk_size` are allocated on the heap individually.
    pub fn new(chunk_size: ChunkSize) -> Self {
        let mut chunk_size = chunk_size.get();

        // Must at least have enough space for the header.
        if chunk_size < STRING_CHUNK_HEADER_SIZE {
            chunk_size += STRING_CHUNK_HEADER_SIZE
        }

        Self {
            chunk_size,
            lookup: MultiMap::new(),
            num_strings: 0,
            generation: 0,
            chunks: Vec::new(),
            last_used_chunk: None,
            gc: Vec::new(),
            offsets: Vec::new(),
        }
    }

    /// Returns the number of unique [`interned`](Pool::intern) strings in the [`Pool`].
    ///
    /// NOTE - includes strings which have been removed via [`remove_gc`](Pool::remove_gc),
    /// but not yet garbage collected via [`gc`](Pool::gc).
    pub fn len(&self) -> usize {
        self.num_strings as _
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Interns the `string`, returning the [`ID`]
    /// which may later be used to [`look it up`](Pool::lookup) or [`remove`](Pool::remove) it from the [`Pool`].
    ///
    /// If the `string` was already interned, returns the same [`ID`] as the one returned by the previous call to `intern`,
    /// internally incrementing the `string`'s ref count.
    ///
    /// Accepts things convertible to [`Cow<str>`] by value as a slight optimiziation
    /// to avoid allocating a new string on the heap in case when
    /// 1) it would need to be allocated on the heap (because it is too large), and
    /// 2) it's already a [`String`].
    /// Should have no effect otherwise, except maybe monomorphization cost.
    ///
    /// # Errors
    ///
    /// - Returns an [`error`](Error::EmptyString) if the string is empty.
    /// - Returns an [`error`](Error::RefCountOverflow) if the string's ref count overflows.
    /// - Returns an [`error`](Error::StringCountOverflow) if the total string count overflows.
    pub fn intern<'s, S: Into<Cow<'s, str>>>(&mut self, string: S) -> Result<ID, Error> {
        if self.num_strings >= MAX_NUM_STRINGS {
            return Err(Error::StringCountOverflow(MAX_NUM_STRINGS as _));
        }

        let cow: Cow<'_, str> = string.into();
        let string: &str = &cow;

        let length = string.len();

        if length == 0 {
            return Err(Error::EmptyString);
        }

        let data_size = Self::data_size(self.chunk_size);

        // Hash the string.
        let hash = string_hash_fnv1a(string);

        // The string(s) with this hash was (were) interned
        // (but might have been `remove_gc`'d and not yet `gc`'d).
        let generation = if let Some(mut strings) = self.lookup.entry(hash) {
            for string_state in strings.iter_mut() {
                // Look up the string in the chunk.
                let looked_up_string = string_state.lookup(data_size);

                // The strings are the same - increment the ref count and return the existing `ID`.
                if string == looked_up_string {
                    // NOTE - ref count might have been `0` if the string was `remove_gc`'d and not yet `gc`'d -
                    // `gc` will skip strings with non-`0` ref counts.
                    string_state.ref_count = string_state
                        .ref_count
                        .checked_add(1)
                        .ok_or(Error::RefCountOverflow(RefCount::MAX as _))?;

                    return Ok(ID {
                        hash,
                        generation: string_state.generation,
                    });
                }
            }

            // (Cold case) None of the strings match - we've got a hash collision.
            // Must intern with a new `ID`.
            let (new_state, generation) = Self::intern_new_string(
                cow,
                &mut self.last_used_chunk,
                &mut self.chunks,
                &mut self.num_strings,
                &mut self.generation,
                self.chunk_size,
            );

            strings.insert(new_state);

            generation

            // Else the string with this hash has not been interned yet.
            // Intern it and return the new `ID`.
        } else {
            let (new_state, generation) = Self::intern_new_string(
                cow,
                &mut self.last_used_chunk,
                &mut self.chunks,
                &mut self.num_strings,
                &mut self.generation,
                self.chunk_size,
            );

            let _none = self.lookup.insert(hash, new_state);
            debug_assert_eq!(_none, 0);

            generation
        };

        Ok(ID { hash, generation })
    }

    /// Same as [`intern`](Pool::intern), but accepts string slices only.
    ///
    /// Use to minimize monomorphization costs during compilation if only working with string slices.
    pub fn intern_str(&mut self, string: &str) -> Result<ID, Error> {
        self.intern(string)
    }

    /// Internally increments the ref count of the string, previously [`intern`](Pool::intern)'ed with string [`id`](ID).
    ///
    /// # Errors
    ///
    /// - Returns an [`error`](Error::InvalidStringID) if the [`id`](ID) is invalid.
    /// - Returns an [`error`](Error::RefCountOverflow) if the string's ref count overflows.
    pub fn copy(&mut self, id: ID) -> Result<(), Error> {
        if let Some(string) = self
            .lookup
            .get_iter_mut(&id.hash)
            // Generations match - the `id` is valid
            // (or the generation counter overflowed - but we assume this will never happen; 4 billion unique strings should be enough for everyone).
            .find(|string| string.generation == id.generation)
        {
            // Increment the ref count.
            // NOTE - ref count might have been `0` if the string was `remove_gc`'d and not yet `gc`'d -
            // `gc` will skip strings with non-`0` ref counts.
            string.ref_count = string
                .ref_count
                .checked_add(1)
                .ok_or(Error::RefCountOverflow(RefCount::MAX as _))?;
            Ok(())
        // Else no string with this hash was interned (or was already removed, or `id` is even from a different string pool).
        } else {
            Err(Error::InvalidStringID)
        }
    }

    /// Looks up a previously [`intern`](Pool::intern)'ed string via its string [`id`](ID).
    ///
    /// Returns `None` if the string [`id`](ID) is not valid.
    pub fn lookup(&self, id: ID) -> Option<&str> {
        self.lookup
            .get_iter(&id.hash)
            .filter_map(|string| self.lookup_in_state(string, id.generation))
            .next()
    }

    /// Looks up a previously [`intern`](Pool::intern)'ed string via its string [`id`](ID).
    ///
    /// Returns `None` if the string [`id`](ID) is not valid.
    ///
    /// For use in multithreaded scenarios, in conjunction with [`Mutex`](https://doc.rust-lang.org/1.60.0/std/sync/struct.Mutex.html) / [`RwLock`](https://doc.rust-lang.org/1.60.0/std/sync/struct.RwLock.html).
    ///
    /// # Safety
    ///
    /// Unsafe because the returned string points to the internal memory of the [`Pool`],
    /// which may get overwritten by a call to [`remove`](Pool::remove) - it's up to the
    /// user to ensure [`remove_gc`](Pool::remove_gc) / [`gc`](Pool::gc) are used appropriately instead.
    pub unsafe fn lookup_unsafe(&self, id: ID) -> Option<UnsafeStr> {
        self.lookup(id).map(|string| UnsafeStr::from_str(string))
    }

    /// Internally decrements the ref count associated with the string [`id`](ID) of a previously [`intern`](Pool::intern)'ed string.
    ///
    /// When the ref count reaches zero, the string is removed from the pool - it may no longer be [`looked up`](Pool::lookup).
    /// May invalidate the previously [`looked up`](Pool::lookup_unsafe) strings.
    ///
    /// # Errors
    ///
    /// Returns an [`error`](Error::InvalidStringID) if the [`id`](ID) is invalid.
    pub fn remove(&mut self, id: ID) -> Result<(), Error> {
        Self::remove_string(
            id,
            &mut self.lookup,
            &mut self.chunks,
            &mut self.num_strings,
            false,
            self.chunk_size,
            &mut self.offsets,
        )
    }

    /// Internally decrements the ref count associated with the string [`id`](ID) of a previously [`intern`](Pool::intern)'ed string.
    ///
    /// When the ref count reaches zero, the string is marked for removal from the [`Pool`],
    /// but its memory is not immediately cleaned up - it may no longer be [`looked up`](Pool::lookup),
    /// but does not invalidate the previously [`looked up`](Pool::lookup_unsafe) strings.
    ///
    /// A call to [`gc`](Pool::gc) is required to actually free the memory of strings removed via this method.
    ///
    /// # Errors
    ///
    /// Returns an [`error`](Error::InvalidStringID) if the [`id`](ID) is invalid.
    pub fn remove_gc(&mut self, id: ID) -> Result<(), Error> {
        // The string with this hash was interned (but might have been `remove_gc`'d and not yet `gc`'d).
        if let Some(strings) = self.lookup.get_mut(&id.hash) {
            for string in strings {
                // Generations match - the `id` is valid
                // (or the generation counter overflowed - but we assume this will never happen; 4 billion unique strings should be enough for everyone).
                if string.generation == id.generation {
                    // Attempted to remove a stale `id` which was `remove_gc`'d and not yet `gc`'d.
                    if string.ref_count == 0 {
                        return Err(Error::InvalidStringID);

                    // Otherwise decrement the ref count.
                    } else {
                        string.ref_count -= 1;

                        // This was the last use of this string - mark it for garbage collection.
                        if string.ref_count == 0 {
                            self.gc.push(id);

                            debug_assert!(self.num_strings > 0);
                            self.num_strings -= 1;
                        }

                        return Ok(());
                    }
                }
                // Mismatched generations - the `id` is for a hash-colliding string, is stale (or even from a different string pool).
            }
        }

        // Else no string with this hash was interned (or was already removed);
        // or all string generations were mismatched.
        Err(Error::InvalidStringID)
    }

    /// Frees the memory of the strings, previously removed via [`remove_gc`](Pool::remove_gc).
    ///
    /// May invalidate the previously [`looked up`](Pool::lookup_unsafe) strings.
    pub fn gc(&mut self) {
        while let Some(id) = self.gc.pop() {
            // Drop the errors.
            // TODO: return some error?
            let _ = Self::remove_string(
                id,
                &mut self.lookup,
                &mut self.chunks,
                &mut self.num_strings,
                true,
                self.chunk_size,
                &mut self.offsets,
            );
        }
    }

    /// Returns an iterator over all ([`id`](ID), `&str`) tuples for all strings interned in the [`Pool`].
    pub fn iter(&self) -> impl Iterator<Item = (ID, &'_ str)> {
        StringPoolIter {
            pool: &self,
            iter: self.lookup.multi_iter(),
        }
    }

    fn intern_new_string<'s>(
        cow: Cow<'s, str>,
        last_used_chunk: &mut Option<NonNull<Chunk>>,
        string_chunks: &mut Vec<NonNull<Chunk>>,
        num_strings: &mut u32,
        generation: &mut Generation,
        chunk_size: ChunkSizeInternal,
    ) -> (State, Generation) {
        let cur_generation = *generation;

        let mut increment_counters = || {
            // Increment the generation counter for a new unique string.
            // NOTE - the generation counter may overflow if we insert more than ~4 billion unique strings.
            *generation = generation.wrapping_add(1);

            // Overflow not allowed by the calling code.
            *num_strings += 1;
        };

        let string = &cow;
        let len = string.len();

        // If the string is too large for our chunk size, allocate it on the heap and return it.
        if len > Self::data_size(chunk_size) as usize {
            let state = State::new_string(cur_generation, cow.into_owned());

            increment_counters();

            return (state, cur_generation);
        }

        let mut intern_in_chunk =
            |mut string_chunk: NonNull<Chunk>| -> Option<(State, Generation)> {
                if let InternResult::Interned(lookup_index) =
                    unsafe { string_chunk.as_mut() }.intern(string, Self::data_size(chunk_size))
                {
                    let state = State::new_chunk(cur_generation, string_chunk, lookup_index);

                    increment_counters();

                    Some((state, cur_generation))
                } else {
                    None
                }
            };

        // Try to intern in the last used chunk.
        if let Some(last_used_chunk) = last_used_chunk {
            // Successfully interned in the last used chunk.
            if let Some(res) = intern_in_chunk(*last_used_chunk) {
                return res;
            }
        }

        // Failed to intern in the last used chunk -
        // try to intern in all chunks in order.
        for string_chunk in string_chunks.iter_mut() {
            // Already checked and failed above.
            if Some(*string_chunk) == *last_used_chunk {
                continue;
            }

            // Successfully interned in the current chunk.
            if let Some(res) = intern_in_chunk(*string_chunk) {
                // Update the `last_used_chunk`.
                last_used_chunk.replace(*string_chunk);
                return res;
            }
        }

        // No chunks / no space in all chunks - allocate a new one.
        let new_chunk = Chunk::allocate(chunk_size);

        // Add it to the chunk array.
        string_chunks.push(new_chunk);

        // Must succeed - the chunk is guaranteed to have enough space.
        let res = unsafe { intern_in_chunk(new_chunk).unwrap_unchecked_dbg() };
        // Update the `last_used_chunk`.
        *last_used_chunk = Some(new_chunk);
        res
    }

    fn remove_string(
        id: ID,
        lookup: &mut MultiMap<Hash, State>,
        chunks: &mut Vec<NonNull<Chunk>>,
        num_strings: &mut u32,
        gc: bool,
        chunk_size: ChunkSizeInternal,
        offsets: &mut Vec<(StringInChunk, Offset)>,
    ) -> Result<(), Error> {
        // The string with this hash was interned (but might have been `remove_gc`'d and not yet `gc`'d).
        if let Some(mut strings) = lookup.entry(id.hash) {
            for (index, string) in strings.iter_mut().enumerate() {
                // Generations match - the `id` is valid
                // (or the generation counter overflowed - but we assume this will never happen; 4 billion unique strings should be enough for everyone).
                if string.generation == id.generation {
                    if !gc {
                        // Attempted to remove a stale `id` which was `remove_gc`'d and not yet `gc`'d.
                        if string.ref_count == 0 {
                            return Err(Error::InvalidStringID);
                        }

                        // Decrement the ref count.
                        string.ref_count -= 1;
                    }

                    // `remove_gc`'d and about to be `gc`'d,
                    // or this was the last use of this string when the ref count decremented above.
                    if string.ref_count == 0 {
                        if let Storage::Chunk(string_state) = &string.storage {
                            Self::remove_string_from_chunk(
                                string_state.chunk,
                                string_state.index,
                                chunks,
                                num_strings,
                                gc,
                                chunk_size,
                                offsets,
                            );
                        }

                        // Remove the string from the state array.
                        unsafe { strings.remove_unchecked(index) };
                    }

                    // Else the string might've been re-interned / copied
                    // before we garbage collected it.

                    return Ok(());
                }

                // Else, mismatched generations - the `id` is for a hash-colliding string,
                // or is stale (or even from a different string pool).
            }
        }

        // Else no string with this hash was interned (or was already removed);
        // or all string generations were mismatched.
        Err(Error::InvalidStringID)
    }

    fn remove_string_from_chunk(
        mut chunk_ptr: NonNull<Chunk>,
        index: LookupIndex,
        chunks: &mut Vec<NonNull<Chunk>>,
        num_strings: &mut u32,
        gc: bool,
        chunk_size: ChunkSizeInternal,
        offsets: &mut Vec<(StringInChunk, Offset)>,
    ) {
        let chunk = unsafe { chunk_ptr.as_mut() };

        // This was the last string in the chunk and it's now empty - free it.
        if let RemoveResult::ChunkFree = chunk.remove(index, Self::data_size(chunk_size), offsets) {
            Chunk::free(chunk_ptr, chunk_size);
            chunks.retain(|chunk| *chunk != chunk_ptr);
        }

        if !gc {
            debug_assert!(*num_strings > 0);
            *num_strings -= 1;
        }
    }

    /// Returns the maximum useful length in bytes of the string chunk of `chunk_size`
    /// (i.e. accounts for the string header overhead).
    fn data_size(chunk_size: ChunkSizeInternal) -> ChunkSizeInternal {
        debug_assert!(chunk_size > STRING_CHUNK_HEADER_SIZE);
        chunk_size - STRING_CHUNK_HEADER_SIZE
    }

    fn lookup_in_state<'a>(&self, state: &'a State, generation: Generation) -> Option<&'a str> {
        // Generations match - the `id` is valid
        // (or the generation counter overflowed - but we assume this will never happen; 4 billion unique strings should be enough for everyone).
        if state.generation == generation {
            self.lookup_in_state_impl(state).map(|(string, _)| string)

            // Else, mismatched generations - the `id` is for a hash-colliding string,
            // or is stale (or even from a different string pool).
        } else {
            None
        }
    }

    fn lookup_in_state_impl<'a>(&self, state: &'a State) -> Option<(&'a str, Generation)> {
        if state.ref_count > 0 {
            Some((
                state.lookup(Self::data_size(self.chunk_size)),
                state.generation,
            ))
        // Attempted to look up a stale `id` which was `remove_gc`'d and not yet `gc`'d.
        } else {
            None
        }
    }
}

struct StringPoolIter<'a, I>
where
    I: Iterator<Item = (&'a Hash, &'a State)>,
{
    pool: &'a Pool,
    iter: I,
}

impl<'a, I> Iterator for StringPoolIter<'a, I>
where
    I: Iterator<Item = (&'a Hash, &'a State)>,
{
    type Item = (ID, &'a str);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().and_then(|(&string_hash, string_state)| {
            self.pool
                .lookup_in_state_impl(string_state)
                .map(|(string, generation)| {
                    (
                        ID {
                            hash: string_hash,
                            generation,
                        },
                        string,
                    )
                })
        })
    }
}

impl Drop for Pool {
    fn drop(&mut self) {
        while let Some(chunk) = self.chunks.pop() {
            Chunk::free(chunk, self.chunk_size);
        }
    }
}

#[cfg(test)]
mod tests {
    #![allow(non_snake_case)]

    use super::*;

    const CHUNK_SIZE: ChunkSize = unsafe { ChunkSize::new_unchecked(8) };

    #[test]
    fn EmptyString() {
        let mut pool = Pool::new(CHUNK_SIZE);

        assert_eq!(pool.intern(""), Err(Error::EmptyString));
    }

    #[test]
    fn hash_collisions() {
        // See `fnv1a_hash_collisions()`

        let mut pool = Pool::new(CHUNK_SIZE);

        let costarring_id = pool.intern("costarring").unwrap();
        let liquid_id = pool.intern("liquid").unwrap();

        assert_ne!(costarring_id, liquid_id);

        assert_eq!(pool.lookup(costarring_id).unwrap(), "costarring");
        assert_eq!(pool.lookup(liquid_id).unwrap(), "liquid");
    }

    #[test]
    fn string_pool() {
        let mut pool = Pool::new(CHUNK_SIZE);

        assert_eq!(pool.len(), 0);

        let asdf = "asdf";
        let gh = "gh";

        let asdf_id = pool.intern(asdf).unwrap();

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        // This increments the ref count.
        let asdf_id_2 = pool.intern(asdf).unwrap();

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id_2).unwrap(), asdf);
        assert_eq!(asdf_id, asdf_id_2);

        // This decrements the ref count.
        pool.remove(asdf_id_2).unwrap();

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        // This increments the ref count.
        pool.copy(asdf_id).unwrap();

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        // This decrements the ref count.
        pool.remove(asdf_id).unwrap();

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        let gh_id = pool.intern(gh).unwrap();

        assert_eq!(pool.len(), 2);
        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);
        assert_eq!(pool.lookup(gh_id).unwrap(), gh);

        assert!(gh_id != asdf_id);

        let asdf_unsafe = unsafe { pool.lookup_unsafe(asdf_id).unwrap() };

        unsafe {
            assert_eq!(asdf_unsafe.to_str(), asdf);
        }

        // Should not trigger defragmentation.
        pool.remove_gc(asdf_id).unwrap();

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id), None);
        assert_eq!(pool.remove_gc(asdf_id), Err(Error::InvalidStringID));
        assert_eq!(pool.remove(asdf_id), Err(Error::InvalidStringID));
        assert_eq!(pool.lookup(gh_id).unwrap(), gh);

        // The string may not be looked up any more.
        // But the string data is still there.
        unsafe {
            assert_eq!(asdf_unsafe.to_str(), asdf);
        }

        // Now defragmentation happens, `asdf_unsafe` contains garbage.
        pool.gc();

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id), None);
        assert_eq!(pool.lookup(gh_id).unwrap(), gh);

        // Should allocate a new chunk.
        let long_string = "asdfghjk";

        let long_string_id = pool.intern(long_string).unwrap();

        assert_eq!(pool.len(), 2);
        assert_eq!(pool.lookup(asdf_id), None);
        assert_eq!(pool.lookup(gh_id).unwrap(), gh);
        assert_eq!(pool.lookup(long_string_id).unwrap(), long_string);

        // Should free the first chunk.
        pool.remove(gh_id).unwrap();

        assert_eq!(pool.remove(gh_id), Err(Error::InvalidStringID));
        assert_eq!(pool.remove_gc(gh_id), Err(Error::InvalidStringID));

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id), None);
        assert_eq!(pool.lookup(gh_id), None);
        assert_eq!(pool.lookup(long_string_id).unwrap(), long_string);

        // Should free the last chunk.
        pool.remove(long_string_id).unwrap();

        assert_eq!(pool.remove(long_string_id), Err(Error::InvalidStringID));
        assert_eq!(pool.remove_gc(long_string_id), Err(Error::InvalidStringID));

        assert_eq!(pool.len(), 0);
        assert_eq!(pool.lookup(asdf_id), None);
        assert_eq!(pool.lookup(gh_id), None);
        assert_eq!(pool.lookup(long_string_id), None);
    }

    #[test]
    fn iter() {
        let mut pool = Pool::new(CHUNK_SIZE);

        // Including large strings ("costarring") and colliding strings ("costarring" and "liquid").
        let strings = [
            "foo",
            "bar",
            "baz",
            "bill",
            "bob",
            "barry",
            "costarring",
            "liquid",
        ];

        let mut string_ids = Vec::new();
        let mut bob_id = None;

        for &string in &strings {
            let id = pool.intern(string).unwrap();

            if string == "bob" {
                bob_id.replace(id);
            }

            string_ids.push(id);
        }

        for id in string_ids {
            let string = pool.lookup(id).unwrap();
            assert!(strings.contains(&string));
        }

        for (_, string) in pool.iter() {
            assert!(strings.contains(&string));
        }

        for (k, v) in pool.iter() {
            println!("{:?}: {}", k, v);
        }

        assert_eq!(pool.iter().count(), pool.len());

        pool.remove(bob_id.unwrap()).unwrap();

        for (id, string) in pool.iter() {
            assert!(strings.contains(&string));
            assert_ne!(string, "bob");
            assert_ne!(id, bob_id.unwrap());
        }

        assert_eq!(pool.iter().count(), pool.len());
    }
}
