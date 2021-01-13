use {
    super::{
        error::Error,
        hash::{string_hash_fnv1a, StringHash},
        string_chunk::{
            ChunkSize, ChunkSizeInternal, InternResult, LookupIndex, RemoveResult, StringChunk,
            STRING_CHUNK_HEADER_SIZE,
        },
        string_id::{StringGeneration, StringID},
    },
    std::{collections::HashMap, ptr::NonNull, borrow::Cow},
};

/// Type for the ref count of interned strings.
///
/// Determines how many copies of a string may be interned before an overflow error.
///
/// NOTE - update the docs for `inern` / `copy` when changing this.
type RefCount = u32;

/// String state for either a single (usual case, no hash collisions)
/// or multiple (rare case, hash collision) strings interned in the string pool with a given hash.
/// TODO: refactor the rare hash collision case in a separate lookup array?
enum HashState {
    /// Common case - only one string with this hash.
    Single(StringState),
    /// Rare case - multiple strings with this hash.
    Multiple(Vec<StringState>),
}

/// Storage info for an interned string stored in a chunk.
#[derive(Clone)]
struct ChunkString {
    /// Pointer to the string chunk the string is interned in.
    /// Strings never move between chunks.
    string_chunk: NonNull<StringChunk>,
    /// Index of the element in the string chunk's `lookup` array,
    /// which contains this string's offset from the chunk's data buffer start and its length.
    lookup_index: LookupIndex,
}

impl ChunkString {
    fn string_chunk(&self) -> &StringChunk {
        unsafe { self.string_chunk.as_ref() }
    }
}

/// Type of interned string storage.
#[derive(Clone)]
enum StringStorage {
    /// Most strings are stored in chunks.
    Chunk(ChunkString),
    /// Strings longer than chunk size are stored individually on the heap.
    String(String),
}

/// Interned string info.
#[derive(Clone)]
struct StringState {
    /// Ref count of the interned string.
    ref_count: RefCount,
    /// Generation of the interned string.
    generation: StringGeneration,
    /// The string's storage info - in the chunk or on the heap.
    storage: StringStorage,
}

impl StringState {
    fn new_chunk(
        generation: StringGeneration,
        string_chunk: NonNull<StringChunk>,
        lookup_index: LookupIndex,
    ) -> Self {
        Self {
            ref_count: 1,
            generation,
            storage: StringStorage::Chunk(ChunkString {
                string_chunk,
                lookup_index,
            }),
        }
    }

    fn new_string(generation: StringGeneration, string: String) -> Self {
        Self {
            ref_count: 1,
            generation,
            storage: StringStorage::String(string),
        }
    }

    fn lookup(&self, data_size: ChunkSizeInternal) -> &str {
        match &self.storage {
            StringStorage::Chunk(chunk) => {
                chunk.string_chunk().lookup(chunk.lookup_index, data_size)
            }
            StringStorage::String(string) => string.as_str(),
        }
    }
}

/// A string slice in the [`string pool`] represented as a raw pointer + length.
/// Returned by [`lookup_unsafe`].
/// Used as an escape hatch for `MutexGuard<StringPool>` / `RwLockGuard<StringPool>` string lifetime.
///
/// [`lookup_unsafe`]: struct.StringPool.html#method.lookup_unsafe
/// [`string pool`]: struct.StringPool.html
pub struct UnsafeStr((*const u8, usize));

impl UnsafeStr {
    /// Returns the actual interned string slice.
    ///
    /// # Safety
    ///
    /// Unsafe because it's up to the user to ensure the string does not outlive the [`string pool`]
    /// or is not invalidated by a call to [`remove`].
    ///
    /// [`remove`]: struct.StringPool.html#method.remove
    /// [`string pool`]: struct.StringPool.html
    pub unsafe fn to_str(&self) -> &'static str {
        std::str::from_utf8_unchecked(std::slice::from_raw_parts((self.0).0, (self.0).1))
    }

    unsafe fn from_str(string: &str) -> Self {
        Self((string.as_ptr(), string.len()))
    }
}

/// Manages the collection of unique interned strings.
/// Attempts to store the strings contiguosly in (configurable) fixed-size memory chunks, allocated on demand.
///
/// Uses ref-counting internally to deduplicate stored strings.
pub struct StringPool {
    /// Size in bytes of string chunks, allocated by the string pool to store the strings.
    /// Determines (minus the string hunk header overhead) the max supported interned string length in bytes.
    chunk_size: ChunkSizeInternal,
    /// Maps the string hash to the string state - ref count, generation and chunk / index in chunk.
    lookup: HashMap<StringHash, HashState>,
    /// Total number of unique strings interned in the pool
    /// (including not-yet-garbage-collected strings).
    num_strings: u32,
    /// Current string generation monotonic counter, incremented for each interned unique string.
    /// Used to invalidate removed `StringID`'s.
    generation: StringGeneration,
    /// All chunks allocated by the string pool.
    string_chunks: Vec<NonNull<StringChunk>>,
    /// Cached pointer to the last chunk a string was successfully interned in,
    /// used to slightly speed up the interning operation.
    last_used_chunk: Option<NonNull<StringChunk>>,
    /// String ID's of all strings removed from the string pool via `remove_gc` (their ref count reached `0`),
    /// bot not yet garbage collected.
    gc: Vec<StringID>,
}

impl StringPool {
    /// Creates a new [`string pool`].
    ///
    /// String pool will allocate memory in `chunk_size` byte chunks
    /// (unless `chunk_size` is smaller than the (small) string chunk header overhead,
    /// in which case slightly more memory will be allocated per chunk).
    ///
    /// `chunk_size` determines the max string length in bytes which may be interned in a chunk.
    /// Larger chunks allow for longer strings to be stored, but may have higher memory fragmentation
    /// if the strings are frequently added and removed, as the pool makes no effort to reuse
    /// free space in chunks until it exceeds 50% of the chunk's size.
    /// Strings longer than chunk size are allocated on the heap individually.
    ///
    /// [`string pool`]: struct.StringPool.html
    pub fn new(chunk_size: ChunkSize) -> Self {
        let mut chunk_size = chunk_size.get();

        // Must at least have enough space for the header.
        if chunk_size < STRING_CHUNK_HEADER_SIZE {
            chunk_size += STRING_CHUNK_HEADER_SIZE
        }

        Self {
            chunk_size,
            lookup: HashMap::new(),
            num_strings: 0,
            generation: 0,
            string_chunks: Vec::new(),
            last_used_chunk: None,
            gc: Vec::new(),
        }
    }

    /// Returns the number of unique interned strings in the [`string pool`].
    ///
    /// NOTE - includes strings which have been removed via [`remove_gc`],
    /// but not yet garbage collected via [`gc`].
    ///
    /// [`string pool`]: struct.StringPool.html
    /// [`remove_gc`]: #method.remove_gc
    /// [`gc`]: #method.gc
    pub fn len(&self) -> usize {
        self.num_strings as _
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Interns the `string`, returning the [`StringID`]
    /// which may later be used to [`look it up`] or [`remove`] it from the [`string pool`].
    ///
    /// If `string` was already interned, returns the same [`StringID`] as the one returned by the previous call to `intern`,
    /// internally incrementing the string's ref count.
    ///
    /// Returns an error if the string is empty.
    /// Returns an error if the string's ref count overflows.
    ///
    /// [`StringID`]: struct.StringID.html
    /// [`look it up`]: #method.lookup
    /// [`remove`]: #method.remove
    /// [`string pool`]: struct.StringPool.html
    pub fn intern<'s, S: Into<Cow<'s, str>>>(&mut self, string: S) -> Result<StringID, Error> {
        let cow = string.into();

        let string: &str = &cow;

        let string_length = string.len();

        if string_length == 0 {
            return Err(Error::EmptyString);
        }

        // Hash the string.
        let string_hash = string_hash_fnv1a(string);

        // The string(s) with this hash was (were) interned
        // (but might have been `remove_gc`'d and not yet `gc`'d).
        if let Some(hash_state) = self.lookup.get_mut(&string_hash) {
            match hash_state {
                // There's a single string with this hash.
                HashState::Single(string_state) => {
                    // Look up the string in the chunk to check for hash collisions.
                    let looked_up_string = string_state.lookup(Self::data_size(self.chunk_size));

                    // The strings are the same - increment the ref count and return the existing `StringID`.
                    if string == looked_up_string {
                        // NOTE - ref count might have been `0` if the string was `remove_gc`'d and not yet `gc`'d -
                        // `gc` will skip strings with non-`0` ref counts.
                        string_state.ref_count = string_state
                            .ref_count
                            .checked_add(1)
                            .ok_or(Error::RefCountOverflow(RefCount::MAX as _))?;

                        return Ok(StringID {
                            string_hash,
                            generation: string_state.generation,
                        });

                    // (Cold case) The strings are different - we have a hash collision.
                    // Must intern with a new `StringID` and change the string hash's state to `Multiple`.
                    } else {
                        let new_state = Self::intern_new_string(
                            cow,
                            string_length,
                            &mut self.last_used_chunk,
                            &mut self.string_chunks,
                            &mut self.num_strings,
                            &mut self.generation,
                            self.chunk_size,
                        );

                        let generation = new_state.generation;

                        // Change the hash's state from single to multiple.
                        if let Some(hash_state) = self.lookup.remove(&string_hash) {
                            if let HashState::Single(string_state) = hash_state {
                                self.lookup.insert(
                                    string_hash,
                                    HashState::Multiple(vec![string_state, new_state]),
                                );
                            } else {
                                debug_assert!(false, "unreachable");
                            }
                        } else {
                            debug_assert!(false, "unreachable");
                        }

                        return Ok(StringID {
                            string_hash,
                            generation,
                        });
                    }
                }
                // (Cold case) There are multiple strings with this hash.
                HashState::Multiple(states) => {
                    for string_state in states.iter_mut() {
                        // Look up the string in the chunk.
                        let looked_up_string =
                            string_state.lookup(Self::data_size(self.chunk_size));

                        // The strings are the same - increment the ref count and return the existing `StringID`.
                        if cow == looked_up_string {
                            // NOTE - ref count might have been `0` if the string was `remove_gc`'d and not yet `gc`'d -
                            // `gc` will skip strings with non-`0` ref counts.
                            string_state.ref_count = string_state
                                .ref_count
                                .checked_add(1)
                                .ok_or(Error::RefCountOverflow(RefCount::MAX as _))?;

                            return Ok(StringID {
                                string_hash,
                                generation: string_state.generation,
                            });
                        }
                    }

                    // (Cold case) None of the strings match - we've got yet another hash collision.
                    // Must intern with a new `StringID`.
                    let new_state = Self::intern_new_string(
                        cow,
                        string_length,
                        &mut self.last_used_chunk,
                        &mut self.string_chunks,
                        &mut self.num_strings,
                        &mut self.generation,
                        self.chunk_size,
                    );

                    let generation = new_state.generation;

                    states.push(new_state);

                    return Ok(StringID {
                        string_hash,
                        generation,
                    });
                }
            }
        // Else the string with this hash has not been interned yet.
        // Intern it and return the new `StringID`.
        } else {
            let new_state = Self::intern_new_string(
                cow,
                string_length,
                &mut self.last_used_chunk,
                &mut self.string_chunks,
                &mut self.num_strings,
                &mut self.generation,
                self.chunk_size,
            );

            let generation = new_state.generation;

            let _none = self
                .lookup
                .insert(string_hash, HashState::Single(new_state));
            debug_assert!(_none.is_none());

            return Ok(StringID {
                string_hash,
                generation,
            });
        }
    }

    /// Internally increments the ref count of the string, previously [`intern`]'ed with [`string_id`].
    ///
    /// Returns an error if the [`string_id`] is invalid.
    /// Returns an error if the string's ref count overflows.
    ///
    /// [`intern`]: #method.intern
    /// [`string_id`]: struct.StringID.html
    pub fn copy(&mut self, string_id: StringID) -> Result<(), Error> {
        // The string with this hash was interned (but might have been `remove_gc`'d and not yet `gc`'d).
        if let Some(hash_state) = self.lookup.get_mut(&string_id.string_hash) {
            match hash_state {
                // There's a single string with this hash.
                HashState::Single(string_state) => {
                    // Generations match - the `string_id` is valid
                    // (or the generation counter overflowed - but we assume this will never happen; 4 billion unique strings should be enough for everyone).
                    if string_state.generation == string_id.generation {
                        string_state.ref_count = string_state
                            .ref_count
                            .checked_add(1)
                            .ok_or(Error::RefCountOverflow(RefCount::MAX as _))?;

                        Ok(())

                    // Mismatched generations - the `string_id` is stale (or even from a different string pool).
                    } else {
                        Err(Error::InvalidStringID)
                    }
                }
                // (Cold case) There are multiple strings with this hash.
                HashState::Multiple(states) => {
                    debug_assert!(states.len() > 1);

                    for string_state in states.iter_mut() {
                        if string_state.generation == string_id.generation {
                            string_state.ref_count = string_state
                                .ref_count
                                .checked_add(1)
                                .ok_or(Error::RefCountOverflow(RefCount::MAX as _))?;

                            return Ok(());
                        }
                        // Else, mismatched generations - the `string_id` is for a hash-colliding string,
                        // or is stale (or even from a different string pool).
                    }

                    Err(Error::InvalidStringID)
                }
            }

        // Else no string with this hash was interned (or was already removed).
        } else {
            Err(Error::InvalidStringID)
        }
    }

    /// Looks up a previously [`intern`]'ed string via its [`string_id`].
    ///
    /// Returns an error if the [`string_id`] is invalid.
    ///
    /// [`intern`]: #method.intern
    /// [`string_id`]: struct.StringID.html
    pub fn lookup(&self, string_id: StringID) -> Result<&str, Error> {
        let lookup_in_state =
            |state: &StringState, generation: StringGeneration| -> Result<&str, Error> {
                // Generations match - the `string_id` is valid
                // (or the generation counter overflowed - but we assume this will never happen; 4 billion unique strings should be enough for everyone).
                if state.generation == generation {
                    // Attempted to look up a stale `string_id` which was `remove_gc`'d and not yet `gc`'d.
                    if state.ref_count == 0 {
                        Err(Error::InvalidStringID)
                    } else {
                        // TODO - review the safety of this.
                        Ok(unsafe {
                            std::mem::transmute(state.lookup(Self::data_size(self.chunk_size)))
                        })
                    }

                // Else, mismatched generations - the `string_id` is for a hash-colliding string,
                // or is stale (or even from a different string pool).
                } else {
                    Err(Error::InvalidStringID)
                }
            };

        // The string with this hash was interned (but might have been `remove_gc`'d and not yet `gc`'d).
        if let Some(hash_state) = self.lookup.get(&string_id.string_hash) {
            match hash_state {
                // There's a single string with this hash.
                HashState::Single(string_state) => {
                    lookup_in_state(string_state, string_id.generation)
                }
                // (Cold case) There are multiple strings with this hash.
                HashState::Multiple(states) => {
                    debug_assert!(states.len() > 1);

                    for string_state in states.iter() {
                        if let Ok(string) = lookup_in_state(string_state, string_id.generation) {
                            return Ok(string);
                        }
                    }

                    Err(Error::InvalidStringID)
                }
            }

        // Else no string with this hash was interned (or was already removed).
        } else {
            Err(Error::InvalidStringID)
        }
    }

    /// Looks up a previously [`intern`]'ed string via its [`string_id`].
    ///
    /// Returns an error if the [`string_id`] is invalid.
    ///
    /// For use in multithreaded scenarios, in conjunction with `Mutex` / `RwLock`.
    ///
    /// # Safety
    ///
    /// Unsafe because the returned string points to the internal memory of the string pool,
    /// which may get overwritten by a call to [`remove`] - it's up to the
    /// user to ensure [`remove_gc`] / [`gc`] are used instead.
    ///
    /// [`intern`]: #method.intern
    /// [`string_id`]: struct.StringID.html
    /// [`remove`]: #method.remove
    /// [`remove_gc`]: #method.remove_gc
    /// [`gc`]: #method.gc
    pub unsafe fn lookup_unsafe(&self, string_id: StringID) -> Result<UnsafeStr, Error> {
        self.lookup(string_id)
            .map(|string| UnsafeStr::from_str(string))
    }

    /// Internally decrements the ref count associated with the [`string_id`] of a previously [`intern`]'ed string.
    ///
    /// When the ref count reaches zero, the string is removed from the pool - it may no longer be [`looked up`].
    /// May invalidate the previously [`looked up`] strings (including via [`lookup_unsafe`]).
    ///
    /// Returns an error if the [`string_id`] is invalid.
    ///
    /// [`string_id`]: struct.StringID.html
    /// [`intern`]: #method.intern
    /// [`looked up`]: #method.lookup
    /// [`lookup_unsafe`]: #method.lookup_unsafe
    pub fn remove(&mut self, string_id: StringID) -> Result<(), Error> {
        Self::remove_string(
            string_id,
            &mut self.lookup,
            &mut self.string_chunks,
            &mut self.num_strings,
            false,
            self.chunk_size,
        )
    }

    /// Internally decrements the ref count associated with the [`string_id`] of a previously [`intern`]'ed string.
    ///
    /// When the ref count reaches zero, the string is marked for removal from the pool,
    /// but its memory is not immediately cleaned up - it may no longer be [`looked up`],
    /// but does not invalidate the previously [`looked up`] strings (including via [`lookup_unsafe`]).
    ///
    /// A call to [`gc`] is required to actually free the memory of strings removed via this method.
    ///
    /// Returns an error if the [`string_id`] is invalid.
    ///
    /// [`intern`]: #method.intern
    /// [`string_id`]: struct.StringID.html
    /// [`looked up`]: #method.lookup
    /// [`lookup_unsafe`]: #method.lookup_unsafe
    /// [`gc`]: #method.gc
    pub fn remove_gc(&mut self, string_id: StringID) -> Result<(), Error> {
        // The string with this hash was interned (but might have been `remove_gc`'d and not yet `gc`'d).
        if let Some(hash_state) = self.lookup.get_mut(&string_id.string_hash) {
            match hash_state {
                // There's a single string with this hash.
                HashState::Single(string_state) => {
                    // Generations match - the `string_id` is valid
                    // (or the generation counter overflowed - but we assume this will never happen; 4 billion unique strings should be enough for everyone).
                    if string_state.generation == string_id.generation {
                        // Attempted to remove a stale `string_id` which was `remove_gc`'d and not yet `gc`'d.
                        if string_state.ref_count == 0 {
                            Err(Error::InvalidStringID)

                        // Otherwise decrement the ref count.
                        } else {
                            string_state.ref_count -= 1;

                            // This was the last use of this string - mark it for garbage collection.
                            if string_state.ref_count == 0 {
                                self.gc.push(string_id);

                                debug_assert!(self.num_strings > 0);
                                self.num_strings -= 1;
                            }

                            Ok(())
                        }

                    // Mismatched generations - the `string_id` is stale (or even from a different string pool).
                    } else {
                        Err(Error::InvalidStringID)
                    }
                }
                // (Cold case) There are multiple strings with this hash.
                HashState::Multiple(states) => {
                    debug_assert!(states.len() > 1);

                    for string_state in states.iter_mut() {
                        // Generations match - the `string_id` is valid
                        // (or the generation counter overflowed - but we assume this will never happen; 4 billion unique strings should be enough for everyone).
                        if string_state.generation == string_id.generation {
                            // Attempted to remove a stale `string_id` which was `remove_gc`'d and not yet `gc`'d.
                            if string_state.ref_count == 0 {
                                return Err(Error::InvalidStringID);

                            // Otherwise decrement the ref count.
                            } else {
                                string_state.ref_count -= 1;

                                // This was the last use of this string - mark it for garbage collection.
                                if string_state.ref_count == 0 {
                                    self.gc.push(string_id);

                                    debug_assert!(self.num_strings > 0);
                                    self.num_strings -= 1;
                                }

                                return Ok(());
                            }

                        // Mismatched generations - the `string_id` is for a hash-colliding string, is stale (or even from a different string pool).
                        } else {
                            continue;
                        }
                    }

                    Err(Error::InvalidStringID)
                }
            }

        // Else no string with this hash was interned (or was already removed).
        } else {
            Err(Error::InvalidStringID)
        }
    }

    /// Frees the memory of the strings, previously removed via [`remove_gc`].
    ///
    /// May invalidate the previously [`looked up`] strings (including via [`lookup_unsafe`]).
    ///
    /// [`remove_gc`]: #method.remove_gc
    /// [`looked up`]: #method.lookup
    /// [`lookup_unsafe`]: #method.lookup_unsafe
    pub fn gc(&mut self) {
        while let Some(string_id) = self.gc.pop() {
            // Drop the errors.
            // TODO: return some error?
            let _ = Self::remove_string(
                string_id,
                &mut self.lookup,
                &mut self.string_chunks,
                &mut self.num_strings,
                true,
                self.chunk_size,
            );
        }
    }

    fn intern_new_string<'s>(
        cow: Cow<'s, str>,
        length: usize,
        last_used_chunk: &mut Option<NonNull<StringChunk>>,
        string_chunks: &mut Vec<NonNull<StringChunk>>,
        num_strings: &mut u32,
        generation: &mut StringGeneration,
        chunk_size: ChunkSizeInternal,
    ) -> StringState {
        let string = &cow;

        debug_assert_eq!(string.len(), length);

        if length > Self::data_size(chunk_size) as usize {
            let state = StringState::new_string(*generation, cow.into_owned());

            // Increment the generation counter for a new unique string.
            *generation = generation
                .checked_add(1)
                .expect("generation counter overflow");

            *num_strings += 1;

            return state;
        }

        // Try to intern in the last used chunk.
        if let Some(mut last_used_chunk) = last_used_chunk {
            // Successfully interned in the last used chunk.
            if let InternResult::Interned(lookup_index) =
                unsafe { last_used_chunk.as_mut() }.intern(string, Self::data_size(chunk_size))
            {
                let state = StringState::new_chunk(*generation, last_used_chunk, lookup_index);

                // Increment the generation counter for a new unique string.
                *generation = generation
                    .checked_add(1)
                    .expect("generation counter overflow");

                *num_strings += 1;

                return state;
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
            if let InternResult::Interned(lookup_index) =
                unsafe { string_chunk.as_mut() }.intern(string, Self::data_size(chunk_size))
            {
                // Update the `last_used_chunk`.
                *last_used_chunk = Some(*string_chunk);

                let state = StringState::new_chunk(*generation, *string_chunk, lookup_index);

                // Increment the generation counter for a new unique string.
                *generation = generation
                    .checked_add(1)
                    .expect("generation counter overflow");

                *num_strings += 1;

                return state;
            }
        }

        // No chunks / no space in all chunks - allocate a new one.
        let mut new_chunk = StringChunk::allocate(chunk_size);

        // Add it to the chunk array.
        string_chunks.push(new_chunk);

        // Must succeed - the chunk is guaranteed to have enough space.
        if let InternResult::Interned(lookup_index) =
            unsafe { new_chunk.as_mut() }.intern(string, Self::data_size(chunk_size))
        {
            // Update the `last_used_chunk`.
            *last_used_chunk = Some(new_chunk);

            let state = StringState::new_chunk(*generation, new_chunk, lookup_index);

            // Increment the generation counter for a new unique string.
            *generation = generation
                .checked_add(1)
                .expect("generation counter overflow");

            *num_strings += 1;

            return state;
        } else {
            unreachable!();
        }
    }

    fn remove_string(
        string_id: StringID,
        lookup: &mut HashMap<StringHash, HashState>,
        string_chunks: &mut Vec<NonNull<StringChunk>>,
        num_strings: &mut u32,
        gc: bool,
        chunk_size: ChunkSizeInternal,
    ) -> Result<(), Error> {
        // The string with this hash was interned (but might have been `remove_gc`'d and not yet `gc`'d).
        if let Some(hash_state) = lookup.get_mut(&string_id.string_hash) {
            match hash_state {
                // There's a single string with this hash.
                HashState::Single(string_state) => {
                    // Generations match - the `string_id` is valid
                    // (or the generation counter overflowed - but we assume this will never happen; 4 billion unique strings should be enough for everyone).
                    if string_state.generation == string_id.generation {
                        // `remove_gc`'d and not yet `gc`'d.
                        if string_state.ref_count == 0 {
                            if gc {
                                if let StringStorage::Chunk(string_state) = &string_state.storage {
                                    Self::remove_string_from_chunk(
                                        string_state.string_chunk,
                                        string_state.lookup_index,
                                        string_chunks,
                                        num_strings,
                                        gc,
                                        chunk_size,
                                    );
                                }

                                lookup.remove(&string_id.string_hash);

                                Ok(())

                            // Attempted to remove a stale `string_id` which was `remove_gc`'d and not yet `gc`'d.
                            } else {
                                Err(Error::InvalidStringID)
                            }

                        // Otherwise decrement the ref count.
                        } else if !gc {
                            string_state.ref_count -= 1;

                            // This was the last use of this string - remove it from the chunk
                            // and from the lookup map.
                            if string_state.ref_count == 0 {
                                if let StringStorage::Chunk(string_state) = &string_state.storage {
                                    Self::remove_string_from_chunk(
                                        string_state.string_chunk,
                                        string_state.lookup_index,
                                        string_chunks,
                                        num_strings,
                                        gc,
                                        chunk_size,
                                    );
                                }

                                lookup.remove(&string_id.string_hash);
                            }

                            Ok(())

                        // Else the string might've been re-interned / copied
                        // before we garbage collected it.
                        } else {
                            Ok(())
                        }

                    // Mismatched generations - the `string_id` is stale (or even from a different string pool).
                    } else {
                        Err(Error::InvalidStringID)
                    }
                }
                // (Cold case) There are multiple strings with this hash.
                HashState::Multiple(states) => {
                    debug_assert!(states.len() > 1);

                    for (state_idx, string_state) in states.iter_mut().enumerate() {
                        // Generations match - the `string_id` is valid
                        // (or the generation counter overflowed - but we assume this will never happen; 4 billion unique strings should be enough for everyone).
                        if string_state.generation == string_id.generation {
                            if !gc {
                                // Attempted to remove a stale `string_id` which was `remove_gc`'d and not yet `gc`'d.
                                if string_state.ref_count == 0 {
                                    return Err(Error::InvalidStringID);
                                }

                                // Decrement the ref count.
                                string_state.ref_count -= 1;
                            }

                            // `remove_gc`'d and about to be `gc`'d,
                            // or this was the last use of this string when the ref count decremented above.
                            if string_state.ref_count == 0 {
                                if let StringStorage::Chunk(string_state) = &string_state.storage {
                                    Self::remove_string_from_chunk(
                                        string_state.string_chunk,
                                        string_state.lookup_index,
                                        string_chunks,
                                        num_strings,
                                        gc,
                                        chunk_size,
                                    );
                                }

                                // Remove the string from the state array.
                                states.swap_remove(state_idx);

                                // If there's now only a single string left with this hash,
                                // change it from multiple to single.
                                if states.len() == 1 {
                                    *hash_state = HashState::Single(states.pop().unwrap());
                                }

                                return Ok(());

                            // Else the string might've been re-interned / copied
                            // before we garbage collected it.
                            } else {
                                return Ok(());
                            }

                            // Else, mismatched generations - the `string_id` is for a hash-colliding string,
                            // or is stale (or even from a different string pool).
                        }
                    }

                    Err(Error::InvalidStringID)
                }
            }

        // Else no string with this hash was interned (or was already removed).
        } else {
            Err(Error::InvalidStringID)
        }
    }

    fn remove_string_from_chunk(
        mut string_chunk_ptr: NonNull<StringChunk>,
        lookup_index: LookupIndex,
        string_chunks: &mut Vec<NonNull<StringChunk>>,
        num_strings: &mut u32,
        gc: bool,
        chunk_size: ChunkSizeInternal,
    ) {
        let string_chunk = unsafe { string_chunk_ptr.as_mut() };

        // This was the last string in the chunk and it's now empty - free it.
        if let RemoveResult::ChunkFree =
            string_chunk.remove(lookup_index, Self::data_size(chunk_size))
        {
            StringChunk::free(string_chunk_ptr, chunk_size);
            string_chunks.retain(|chunk| *chunk != string_chunk_ptr);
        }

        if !gc {
            debug_assert!(*num_strings > 0);
            *num_strings -= 1;
        }
    }

    fn data_size(chunk_size: ChunkSizeInternal) -> ChunkSizeInternal {
        debug_assert!(chunk_size > STRING_CHUNK_HEADER_SIZE);
        chunk_size - STRING_CHUNK_HEADER_SIZE
    }
}

impl Drop for StringPool {
    fn drop(&mut self) {
        while let Some(chunk) = self.string_chunks.pop() {
            StringChunk::free(chunk, self.chunk_size);
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
        let mut pool = StringPool::new(CHUNK_SIZE);

        assert_eq!(pool.intern(""), Err(Error::EmptyString));
    }

    #[test]
    fn hash_collisions() {
        // See `fnv1a_hash_collisions()`

        let mut pool = StringPool::new(CHUNK_SIZE);

        let costarring_id = pool.intern("costarring").unwrap();
        let liquid_id = pool.intern("liquid").unwrap();

        assert_ne!(costarring_id, liquid_id);

        assert_eq!(pool.lookup(costarring_id).unwrap(), "costarring");
        assert_eq!(pool.lookup(liquid_id).unwrap(), "liquid");
    }

    #[test]
    fn string_pool() {
        let mut pool = StringPool::new(CHUNK_SIZE);

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
        assert_eq!(pool.lookup(asdf_id), Err(Error::InvalidStringID));
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
        assert_eq!(pool.lookup(asdf_id), Err(Error::InvalidStringID));
        assert_eq!(pool.lookup(gh_id).unwrap(), gh);

        // Should allocate a new chunk.
        let long_string = "asdfghjk";

        let long_string_id = pool.intern(long_string).unwrap();

        assert_eq!(pool.len(), 2);
        assert_eq!(pool.lookup(asdf_id), Err(Error::InvalidStringID));
        assert_eq!(pool.lookup(gh_id).unwrap(), gh);
        assert_eq!(pool.lookup(long_string_id).unwrap(), long_string);

        // Should free the first chunk.
        pool.remove(gh_id).unwrap();

        assert_eq!(pool.remove(gh_id), Err(Error::InvalidStringID));
        assert_eq!(pool.remove_gc(gh_id), Err(Error::InvalidStringID));

        assert_eq!(pool.len(), 1);
        assert_eq!(pool.lookup(asdf_id), Err(Error::InvalidStringID));
        assert_eq!(pool.lookup(gh_id), Err(Error::InvalidStringID));
        assert_eq!(pool.lookup(long_string_id).unwrap(), long_string);

        // Should free the last chunk.
        pool.remove(long_string_id).unwrap();

        assert_eq!(pool.remove(long_string_id), Err(Error::InvalidStringID));
        assert_eq!(pool.remove_gc(long_string_id), Err(Error::InvalidStringID));

        assert_eq!(pool.len(), 0);
        assert_eq!(pool.lookup(asdf_id), Err(Error::InvalidStringID));
        assert_eq!(pool.lookup(gh_id), Err(Error::InvalidStringID));
        assert_eq!(pool.lookup(long_string_id), Err(Error::InvalidStringID));
    }
}
