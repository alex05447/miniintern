use {
    crate::*,
    minimultimap::*,
    ministr::*,
    miniunchecked::*,
    std::{borrow::Cow, iter::Iterator, num::NonZeroUsize},
};

/// Type for the ref count of interned strings.
///
/// Determines how many copies of a string may be interned before an overflow error.
///
/// NOTE - update the docs for `intern()` / `copy()` when changing this.
type RefCount = u32;

const MAX_STRING_REF_COUNT: RefCount = RefCount::MAX;

/// Storage info for an interned string stored in a chunk.
#[derive(Clone)]
struct ChunkString {
    /// Pointer to the string chunk the string is interned in.
    /// Strings never move between chunks.
    /// Pointer is always valid, string chunks have a longer lifetime than any `ChunkString` holding on to them.
    chunk: ChunkPtr,
    /// Index of the element in the string chunk's `lookup` array,
    /// which contains this string's offset from the chunk's data buffer start and its length.
    index: LookupIndex,
}

impl ChunkString {
    fn chunk(&self) -> &Chunk {
        unsafe { self.chunk.as_ref() }
    }
}

/// Type of interned string storage (chunk or heap) and its state.
#[derive(Clone)]
enum Storage {
    /// Most strings are stored in chunks.
    /// Holds the pointer to the chunk.
    Chunk(ChunkString),
    /// Strings longer than chunk size are stored individually on the heap as a `NonEmptyString`.
    String(NonEmptyString),
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
    /// Create a new string state for a string stored in the `chunk`` at lookup `index`.
    fn new_chunk(generation: Generation, chunk: ChunkPtr, index: LookupIndex) -> Self {
        Self::new(generation, Storage::Chunk(ChunkString { chunk, index }))
    }

    /// Create a new string state for a `string`` stored on the heap as a `NonEmptyString`
    /// (if the string is too large to fit in our chunks).
    fn new_string(generation: Generation, string: NonEmptyString) -> Self {
        Self::new(generation, Storage::String(string))
    }

    fn new(generation: Generation, storage: Storage) -> Self {
        Self {
            ref_count: 1,
            generation,
            storage,
        }
    }

    /// Returns the string slice of this string state.
    ///
    /// `data_size` is the maximum useful size in bytes of the string chunk's buffer (i.e. excluding the header),
    /// only used for a debug bounds check.
    fn lookup(&self, data_size: ChunkSizeInternal) -> &NonEmptyStr {
        match &self.storage {
            Storage::Chunk(string) => string.chunk().lookup(string.index, data_size),
            Storage::String(string) => string.as_ref(),
        }
    }
}

/// A string slice in the [`Pool`] represented as a raw pointer + length.
/// Returned by [`lookup_unsafe()`](Pool::lookup_unsafe).
///
/// Used as an escape hatch for `MutexGuard<Pool>` / `RwLockGuard<Pool>` string lifetime.
pub struct UnsafeNonEmptyStr((*const u8, NonZeroUsize));

impl UnsafeNonEmptyStr {
    /// Returns the actual interned string slice.
    ///
    /// # Safety
    ///
    /// Unsafe because it's up to the user to ensure the string does not outlive the [`Pool`]
    /// or is not invalidated by a call to [`remove()`](Pool::remove).
    pub unsafe fn to_nestr(&self) -> &'static NonEmptyStr {
        unsafe {
            NonEmptyStr::new_unchecked(std::str::from_utf8_unchecked(std::slice::from_raw_parts(
                (self.0).0,
                (self.0).1.get(),
            )))
        }
    }

    unsafe fn from_nestr(string: &NonEmptyStr) -> Self {
        Self((string.as_ptr(), string.len_nonzero()))
    }
}

/// Type for the total number of unique interned strings.
///
/// Determines how many unique strings may be interned before an overflow error.
///
/// NOTE - update the docs for `intern()` when changing this.
type NumStrings = u32;

const MAX_NUM_STRINGS: NumStrings = NumStrings::MAX;

/// String pool / arena.
///
/// Manages a collection of unique non-empty interned strings and associates them with opaque unique [`identifiers`](ID).
/// Attempts to store the strings contiguosly in (configurable) fixed-size memory chunks, allocated on demand.
///
/// Uses ref-counting internally to deduplicate stored strings,
/// and intermittent defragmentation on remove to compact used memory.
pub struct Pool {
    /// Size in bytes of string chunks allocated by this pool to store the strings small enough to fit.
    /// Determines (minus the string chunk header overhead) the max supported interned string length in bytes.
    chunk_size: ChunkSizeInternal,
    /// Maps the string hash to (one or multiple, in case of hash collisions) string state(s) - ref count, generation and storage (chunk / heap).
    lookup: MultiMap<Hash, State>,
    /// Total number of unique strings interned in the pool
    /// (including not-yet-garbage-collected strings).
    num_strings: NumStrings,
    /// Current string generation monotonic counter, incremented for each interned unique string.
    /// Used to invalidate removed `ID`'s.
    generation: Generation,
    /// All chunks allocated by the pool.
    chunks: Vec<ChunkPtr>,
    /// Cached pointer to the last chunk a string was successfully interned in,
    /// used to slightly speed up the interning operation.
    last_used_chunk: Option<ChunkPtr>,
    /// String ID's of all strings removed from the string pool via `remove_gc` (their ref count reached `0`),
    /// bot not yet garbage collected.
    gc: Vec<ID>,
    /// Scratch pad vec used for string chunk defragmenting.
    /// Persisted and reused to avoid allocating a new one in each call to `defragment`.
    offsets: Vec<(StringInChunk, Offset)>,
}

enum RemoveMode {
    // Decrement ref count, remove string from lookup, decrement number of strings.
    Remove,
    // Decrement ref count, do not remove string from lookup, decrement number of strings.
    RemoveGC,
    // Do not decrement ref count, remove string from lookup, do not decrement number of strings.
    GC,
}

impl RemoveMode {
    fn dec_counters(&self) -> bool {
        matches!(self, RemoveMode::Remove | RemoveMode::RemoveGC)
    }

    fn remove(&self) -> bool {
        matches!(self, RemoveMode::Remove | RemoveMode::GC)
    }
}

impl Pool {
    /// Creates a new string [`Pool`].
    ///
    /// [`Pool`] will allocate memory in `chunk_size`-byte chunks
    /// (unless `chunk_size` is smaller than the (small) string chunk header overhead,
    /// in which case slightly more memory will be allocated per chunk).
    ///
    /// `chunk_size` determines the max string length in bytes which may be interned in a chunk.
    /// Larger chunks allow for longer strings to be stored, but may have higher memory fragmentation
    /// if the strings are frequently added and removed, as the pool currently makes no effort to reuse
    /// free space in chunks until it exceeds 50% of the chunk's size.
    /// Strings longer than `chunk_size` are allocated on the heap individually.
    pub fn new(chunk_size: ChunkSize) -> Self {
        let mut chunk_size = chunk_size.get();

        // Must at least have enough space for the header.
        if chunk_size < CHUNK_HEADER_SIZE {
            chunk_size += CHUNK_HEADER_SIZE
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

    /// Returns the current number of unique [`intern()`](Pool::intern)'ed strings in the [`Pool`].
    ///
    /// NOTE - includes strings which have been removed via [`remove_gc()`](Pool::remove_gc),
    /// but not yet garbage collected via [`gc()`](Pool::gc).
    pub fn len(&self) -> usize {
        self.num_strings as _
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Interns the `string`, returning its [`ID`],
    /// which may later be used to [`lookup()`](Pool::lookup) or [`remove()`](Pool::remove) it from this [`Pool`].
    ///
    /// If the `string` was already interned, returns the same [`ID`] as the one returned by the previous call to [`intern()`](Pool::intern),
    /// internally incrementing the `string`'s ref count.
    ///
    /// Accepts things convertible to [`Cow<NonEmptyStr>`] by value as a slight optimiziation
    /// to avoid allocating a new string on the heap in case when
    /// 1) it would need to be allocated on the heap (because it is too large for the chunk size with which this [`Pool`] was created), and
    /// 2) it's already an owned [`NonEmptyString`].
    /// Should have no effect otherwise, except maybe monomorphization cost.
    ///
    /// # Errors
    ///
    /// - Returns an [`error`](Error::RefCountOverflow) if the `string`'s ref count overflows.
    /// - Returns an [`error`](Error::StringCountOverflow) if the total string counter in the [`Pool`] overflows.
    pub fn intern<'s, S: Into<Cow<'s, NonEmptyStr>>>(&mut self, string: S) -> Result<ID, Error> {
        if self.num_strings == MAX_NUM_STRINGS {
            return Err(Error::StringCountOverflow(MAX_NUM_STRINGS as _));
        }

        let cow: Cow<'_, NonEmptyStr> = string.into();

        let string: &NonEmptyStr = &cow;

        let data_size = Self::data_size(self.chunk_size);

        // Hash the string.
        let hash = string_hash_fnv1a(string);

        // Look up the string by the hash.
        let generation = match self.lookup.entry(hash) {
            // The string(s) with this hash was (were) interned
            // (but might have been `remove_gc()`'d and not yet `gc()`'d).
            Entry::Occupied(mut entry) => {
                for string_state in entry.get_mut() {
                    // Look up the string in the chunk.
                    let looked_up_string = string_state.lookup(data_size);

                    // The strings are the same - increment the ref count and return the existing `ID`.
                    if string == looked_up_string {
                        // NOTE - ref count might have been `0` if the string was `remove_gc()`'d and not yet `gc()`'d -
                        // `gc()` will skip strings with non-`0` ref counts.
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

                // Cold case - none of the strings match, we've got a hash collision.
                // Must intern with a new `ID`.
                let (new_state, generation) = Self::intern_new_string(
                    cow,
                    &mut self.last_used_chunk,
                    &mut self.chunks,
                    &mut self.num_strings,
                    &mut self.generation,
                    self.chunk_size,
                );

                entry.push(new_state);

                generation
            }
            // Else the string with this hash has not been interned yet.
            // Intern it and return the new `ID`.
            Entry::Vacant(entry) => {
                let (new_state, generation) = Self::intern_new_string(
                    cow,
                    &mut self.last_used_chunk,
                    &mut self.chunks,
                    &mut self.num_strings,
                    &mut self.generation,
                    self.chunk_size,
                );

                entry.insert(new_state);

                generation
            }
        };

        Ok(ID { hash, generation })
    }

    /// Same as [`intern()`](Pool::intern), but accepts (non-empty) string slices only.
    ///
    /// Use to minimize monomorphization costs during compilation if only working with string slices.
    pub fn intern_str(&mut self, string: &NonEmptyStr) -> Result<ID, Error> {
        self.intern(string)
    }

    /// Internally increments the ref count of the string, previously [`intern()`](Pool::intern)'ed with string [`id`](ID).
    ///
    /// # Errors
    ///
    /// - Returns an [`error`](Error::InvalidStringID) if the [`id`](ID) is invalid.
    /// - Returns an [`error`](Error::RefCountOverflow) if the string's ref count overflows.
    pub fn copy(&mut self, id: ID) -> Result<(), Error> {
        if let Some(string) = self
            .lookup
            .get_mut(&id.hash)
            .map(|strings| {
                // Generations match - the `id` is valid
                // (or the generation counter overflowed - but we assume this will never happen; 4 billion unique strings should be enough for everyone).
                strings
                    .iter_mut()
                    .find(|string| string.generation == id.generation)
            })
            .flatten()
        {
            // Increment the ref count.
            // NOTE - ref count might have been `0` if the string was `remove_gc()`'d and not yet `gc()`'d -
            // `gc()` will skip strings with non-`0` ref counts.
            string.ref_count = string
                .ref_count
                .checked_add(1)
                .ok_or(Error::RefCountOverflow(MAX_STRING_REF_COUNT as _))?;
            Ok(())
        // Else no string with this `id` was interned (or was already removed, or `id` is from a different string pool).
        } else {
            Err(Error::InvalidStringID)
        }
    }

    /// Looks up a previously [`intern()`](Pool::intern)'ed string via its string [`id`](ID).
    ///
    /// Returns `None` if the string [`id`](ID) is not valid.
    pub fn lookup(&self, id: ID) -> Option<&NonEmptyStr> {
        self.lookup
            .get(&id.hash)
            .map(|strings| {
                strings
                    .iter()
                    .filter_map(|string| self.lookup_in_state(string, id.generation))
                    .next()
            })
            .flatten()
    }

    /// Looks up a previously [`intern()`](Pool::intern)'ed string via its string [`id`](ID).
    ///
    /// Returns `None` if the string [`id`](ID) is not valid.
    ///
    /// For use in multithreaded scenarios, in conjunction with [`Mutex`](std::sync::Mutex) / [`RwLock`](std::sync::RwLock).
    ///
    /// # Safety
    ///
    /// Unsafe because the returned [`string`](UnsafeNonEmptyStr) points to the internal memory of the [`Pool`],
    /// which may get overwritten by a concurrent / followup call to [`remove()`](Pool::remove) - it's up to the
    /// user to ensure [`remove_gc()`](Pool::remove_gc) / [`gc()`](Pool::gc) are used appropriately instead.
    pub unsafe fn lookup_unsafe(&self, id: ID) -> Option<UnsafeNonEmptyStr> {
        self.lookup(id)
            .map(|string| UnsafeNonEmptyStr::from_nestr(string))
    }

    /// Internally decrements the ref count associated with the string [`id`](ID) of a previously [`intern()`](Pool::intern)'ed string.
    ///
    /// Returns `true` if the string [`id`](ID) was valid and the string was removed; else returns `false`.
    ///
    /// When the ref count reaches zero, the string is removed from the pool - it may no longer be [`looked up`](Pool::lookup).
    /// May invalidate the previously [`unsafely looked up`](Pool::lookup_unsafe) [`strings`](UnsafeNonEmptyStr).
    pub fn remove(&mut self, id: ID) -> bool {
        Self::remove_string(
            id,
            &mut self.lookup,
            &mut self.chunks,
            &mut self.num_strings,
            RemoveMode::Remove,
            self.chunk_size,
            &mut self.gc,
            &mut self.offsets,
        )
    }

    /// Internally decrements the ref count associated with the string [`id`](ID) of a previously [`intern()`](Pool::intern)'ed string.
    ///
    /// Returns `true` if the string [`id`](ID) was valid and the string was removed; else returns `false`.
    ///
    /// When the ref count reaches zero, the string is marked for removal from the [`Pool`],
    /// but its memory is not immediately cleaned up - it may no longer be [`looked up`](Pool::lookup),
    /// but does not invalidate the previously [`unsafely looked up`](Pool::lookup_unsafe) [`strings`](UnsafeNonEmptyStr).
    ///
    /// A call to [`gc()`](Pool::gc) is required to actually free the memory of strings removed via this method.
    pub fn remove_gc(&mut self, id: ID) -> bool {
        Self::remove_string(
            id,
            &mut self.lookup,
            &mut self.chunks,
            &mut self.num_strings,
            RemoveMode::RemoveGC,
            self.chunk_size,
            &mut self.gc,
            &mut self.offsets,
        )
    }

    /// Frees the memory of the strings, previously removed via [`remove_gc()`](Pool::remove_gc).
    ///
    /// May invalidate the previously [`unsafely looked up`](Pool::lookup_unsafe) strings.
    pub fn gc(&mut self) {
        while let Some(id) = self.gc.pop() {
            // Drop the errors.
            // TODO: return some error?
            let _ = Self::remove_string(
                id,
                &mut self.lookup,
                &mut self.chunks,
                &mut self.num_strings,
                RemoveMode::GC,
                self.chunk_size,
                &mut self.gc,
                &mut self.offsets,
            );
        }
    }

    /// Returns an [`iterator`](PoolIter) over all ([`id`](ID), [`string`](NonEmptyStr)) tuples for all strings interned in the [`Pool`], in unspecified order.
    pub fn iter(&self) -> PoolIter<'_> {
        PoolIter {
            pool: self,
            iter: self.lookup.multi_iter(),
        }
    }

    fn intern_new_string(
        cow: Cow<'_, NonEmptyStr>,
        last_used_chunk: &mut Option<ChunkPtr>,
        chunks: &mut Vec<ChunkPtr>,
        num_strings: &mut NumStrings,
        generation: &mut Generation,
        chunk_size: ChunkSizeInternal,
    ) -> (State, Generation) {
        let cur_generation = *generation;

        let mut increment_counters = || {
            // Increment the generation counter for a new unique string.
            // NOTE - the generation counter may wrap if we insert more than ~4 billion unique strings.
            *generation = generation.wrapping_add(1);

            // Overflow not allowed by the calling code.
            debug_assert!(*num_strings < MAX_NUM_STRINGS);
            *num_strings += 1;
        };

        let string = &cow;
        let len = string.len();

        let data_size = Self::data_size(chunk_size);

        // If the string is too large for our chunk size, allocate it on the heap.
        if len > data_size as _ {
            let state = State::new_string(cur_generation, cow.into_owned());

            increment_counters();

            return (state, cur_generation);
        }

        // Otherwise intern in a string chunk.

        let mut intern_in_chunk = |mut chunk: ChunkPtr| -> Option<(State, Generation)> {
            if let InternResult::Interned(index) =
                unsafe { chunk.as_mut() }.intern(string, data_size)
            {
                let state = State::new_chunk(cur_generation, chunk, index);

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
        // try to intern in all existing chunks in order.
        for chunk in chunks.iter_mut() {
            // Already checked and failed above.
            if Some(*chunk) == *last_used_chunk {
                continue;
            }

            // Successfully interned in the current chunk.
            if let Some(result) = intern_in_chunk(*chunk) {
                // Update the `last_used_chunk`.
                last_used_chunk.replace(*chunk);
                return result;
            }
        }

        // No chunks / no space in all chunks - allocate a new one.
        let new_chunk = Chunk::allocate(chunk_size);

        // Add it to the chunk array.
        chunks.push(new_chunk);

        // Must succeed - the chunk is guaranteed to have enough space.
        let result = unsafe {
            intern_in_chunk(new_chunk)
                .unwrap_unchecked_dbg_msg("failed to intern a string in a newly allocated chunk")
        };
        // Update the `last_used_chunk`.
        *last_used_chunk = Some(new_chunk);
        result
    }

    fn remove_string(
        id: ID,
        lookup: &mut MultiMap<Hash, State>,
        chunks: &mut Vec<ChunkPtr>,
        num_strings: &mut u32,
        mode: RemoveMode,
        chunk_size: ChunkSizeInternal,
        gc: &mut Vec<ID>,
        offsets: &mut Vec<(StringInChunk, Offset)>,
    ) -> bool {
        match lookup.entry(id.hash) {
            // The string with this `id` hash was interned (but might have been `remove_gc()`'d and not yet `gc()`'d).
            Entry::Occupied(mut entry) => {
                for (index, string) in entry.get_mut().iter_mut().enumerate() {
                    // Generations match - the `id` is valid
                    // (or the generation counter overflowed - but we assume this will never happen; 4 billion unique strings should be enough for everyone).
                    if string.generation == id.generation {
                        if mode.dec_counters() {
                            // Decrement the ref count.
                            string.ref_count =
                                if let Some(ref_count) = string.ref_count.checked_sub(1) {
                                    ref_count
                                } else {
                                    // Attempted to remove a stale `id` which was `remove_gc()`'d and not yet `gc()`'d.
                                    return false;
                                }
                        }

                        // `remove_gc()`'d and about to be `gc()`'d,
                        // or this was the last use of this string when the ref count decremented above.
                        if string.ref_count == 0 {
                            if mode.remove() {
                                // If it's a chunk string, remove it from the chunk.
                                if let Storage::Chunk(string) = &string.storage {
                                    Self::remove_string_from_chunk(
                                        string.chunk,
                                        string.index,
                                        chunks,
                                        chunk_size,
                                        offsets,
                                    );
                                }

                                // Remove the string from the state array.
                                let _removed = entry.remove_at(index);
                                debug_assert!(_removed.is_ok());
                            } else {
                                gc.push(id);
                            }

                            if mode.dec_counters() {
                                debug_assert!(*num_strings > 0);
                                *num_strings -= 1;
                            }
                        }

                        // Else the string might've been re-interned / copied
                        // before we garbage collected it.

                        return true;
                    }
                    // Else, mismatched generations - the `id` is for a hash-colliding string,
                    // is stale, or is from a different string pool.
                }
            }
            Entry::Vacant(_) => {}
        }

        // Else no string with this hash was interned (or was already removed);
        // or all string generations were mismatched.
        false
    }

    fn remove_string_from_chunk(
        mut chunk: ChunkPtr,
        index: LookupIndex,
        chunks: &mut Vec<ChunkPtr>,
        chunk_size: ChunkSizeInternal,
        offsets: &mut Vec<(StringInChunk, Offset)>,
    ) {
        let chunk_mut = unsafe { chunk.as_mut() };

        // This was the last string in the chunk and it's now empty - free it.
        if let crate::RemoveResult::ChunkFree =
            chunk_mut.remove(index, Self::data_size(chunk_size), offsets)
        {
            let prev_num_chunks_ = chunks.len();
            debug_assert!(prev_num_chunks_ > 0);
            chunks.retain(|chunk_| *chunk_ != chunk);
            debug_assert_eq!(chunks.len(), prev_num_chunks_ - 1);

            Chunk::free(chunk, chunk_size);
        }
    }

    /// Returns the maximum useful length in bytes of the string chunk of `chunk_size`
    /// (i.e. accounts for the string header overhead).
    fn data_size(chunk_size: ChunkSizeInternal) -> ChunkSizeInternal {
        debug_assert!(chunk_size >= CHUNK_HEADER_SIZE);
        chunk_size - CHUNK_HEADER_SIZE
    }

    fn lookup_in_state<'a>(
        &self,
        state: &'a State,
        generation: Generation,
    ) -> Option<&'a NonEmptyStr> {
        // Generations match - the `id` is valid
        // (or the generation counter overflowed - but we assume this will never happen; 4 billion unique strings should be enough for everyone).
        // Else, mismatched generations - the `id` is for a hash-colliding string,
        // or is stale (or even from a different string pool).
        (state.generation == generation)
            .then(|| self.lookup_in_state_impl(state).map(|(string, _)| string))
            .flatten()
    }

    fn lookup_in_state_impl<'a>(&self, state: &'a State) -> Option<(&'a NonEmptyStr, Generation)> {
        // If ref count is `0`, we attempted to look up a stale `id` which was `remove_gc()`'d and not yet `gc()`'d.
        (state.ref_count > 0).then(|| {
            (
                state.lookup(Self::data_size(self.chunk_size)),
                state.generation,
            )
        })
    }
}

/// Iterator over all ([`id`](ID), [`string`](NonEmptyStr)) tuples for all strings interned in the [`Pool`], in unspecified order.
pub struct PoolIter<'a> {
    pool: &'a Pool,
    iter: MultiIter<'a, Hash, State>,
}

impl<'a> Iterator for PoolIter<'a> {
    type Item = (ID, &'a NonEmptyStr);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().and_then(|(&hash, state)| {
            self.pool
                .lookup_in_state_impl(state)
                .map(|(string, generation)| (ID { hash, generation }, string))
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

    use {super::*, ministr_macro::nestr};

    const CHUNK_SIZE: ChunkSize = unsafe { ChunkSize::new_unchecked(8) };

    #[test]
    fn hash_collisions() {
        // See `fnv1a_hash_collisions()`

        let mut pool = Pool::new(CHUNK_SIZE);

        let costarring_id = pool.intern(nestr!("costarring")).unwrap();
        assert_eq!(pool.len(), 1);

        let liquid_id = pool.intern(nestr!("liquid")).unwrap();
        assert_eq!(pool.len(), 2);

        assert_ne!(costarring_id, liquid_id);

        assert_eq!(pool.lookup(costarring_id).unwrap(), "costarring");
        assert_eq!(pool.lookup(liquid_id).unwrap(), "liquid");
    }

    #[test]
    fn pool() {
        let mut pool = Pool::new(CHUNK_SIZE);

        assert_eq!(pool.len(), 0);

        let asdf = nestr!("asdf");
        let gh = nestr!("gh");

        let asdf_id = pool.intern(asdf).unwrap();

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        // This increments the ref count.
        let asdf_id_2 = pool.intern(asdf).unwrap();

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id_2).unwrap(), asdf);
        assert_eq!(asdf_id, asdf_id_2);

        // This decrements the ref count.
        assert!(pool.remove(asdf_id_2));

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        // This increments the ref count.
        pool.copy(asdf_id).unwrap();

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        // This decrements the ref count.
        assert!(pool.remove(asdf_id));

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);

        let gh_id = pool.intern(gh).unwrap();

        assert_eq!(pool.len(), 2);
        assert_eq!(pool.lookup(asdf_id).unwrap(), asdf);
        assert_eq!(pool.lookup(gh_id).unwrap(), gh);

        assert!(gh_id != asdf_id);

        let asdf_unsafe = unsafe { pool.lookup_unsafe(asdf_id).unwrap() };

        unsafe {
            assert_eq!(asdf_unsafe.to_nestr(), asdf);
        }

        // Should not trigger defragmentation.
        assert!(pool.remove_gc(asdf_id));

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id), None);
        assert!(!pool.remove_gc(asdf_id));
        assert!(!pool.remove(asdf_id));
        assert_eq!(pool.lookup(gh_id).unwrap(), gh);

        // The string may not be looked up any more.
        // But the string data is still there.
        unsafe {
            assert_eq!(asdf_unsafe.to_nestr(), asdf);
        }

        // Now defragmentation happens, `asdf_unsafe` contains garbage.
        pool.gc();

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id), None);
        assert_eq!(pool.lookup(gh_id).unwrap(), gh);

        // Should allocate a new chunk.
        let long_string = nestr!("asdfghjk");

        let long_string_id = pool.intern(long_string).unwrap();

        assert_eq!(pool.len(), 2);
        assert_eq!(pool.lookup(asdf_id), None);
        assert_eq!(pool.lookup(gh_id).unwrap(), gh);
        assert_eq!(pool.lookup(long_string_id).unwrap(), long_string);

        // Should free the first chunk.
        assert!(pool.remove(gh_id));

        assert!(!pool.remove(gh_id));
        assert!(!pool.remove_gc(gh_id));

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id), None);
        assert_eq!(pool.lookup(gh_id), None);
        assert_eq!(pool.lookup(long_string_id).unwrap(), long_string);

        // Should free the last chunk.
        assert!(pool.remove(long_string_id));

        assert!(!pool.remove(long_string_id));
        assert!(!pool.remove_gc(long_string_id));

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
            nestr!("foo"),
            nestr!("bar"),
            nestr!("baz"),
            nestr!("bill"),
            nestr!("bob"),
            nestr!("barry"),
            nestr!("costarring"),
            nestr!("liquid"),
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

        assert_eq!(pool.len(), strings.len());

        for id in string_ids {
            let string = pool.lookup(id).unwrap();
            assert!(strings.contains(&string));
        }

        for (_, string) in pool.iter() {
            assert!(strings.contains(&string));
        }

        assert_eq!(pool.iter().count(), pool.len());

        assert!(pool.remove(bob_id.unwrap()));

        for (id, string) in pool.iter() {
            assert!(strings.contains(&string));
            assert_ne!(string, "bob");
            assert_ne!(id, bob_id.unwrap());
        }

        assert_eq!(pool.iter().count(), pool.len());
    }
}
