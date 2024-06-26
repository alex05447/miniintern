# miniintern

A minimalistic Rust string interning / pooling library.

Originally written for `miniecs` string support in component data.

## **Overview**

https://en.wikipedia.org/wiki/String_interning

https://ourmachinery.com/post/data-structures-part-3-arrays-of-arrays/

## **Motivation**

You have a number of strings and you want to

- deduplicate them (do not store more than one copy of any string in memory),
- be able to compare such interned strings efficiently,

and you are fine with interned strings being immutable.

One additional benefit is because you control how the interned strings are stored in memory, you can make string access more cache efficient.

## **API**

- Create a string `Pool`.

    Pass the desired chunk size in bytes. The `Pool` will allocate memory for strings internally in these contiguous chunks.

    This value also determines the maximum length of the string in bytes which may be interned in the chunk. Strings longer than chunk size fall back to individual allocation on the heap.

    You may create as many `Pool`'s as you need. Each `Pool` is completely independent.
    (However, string `ID`'s from different `Pool`'s must not be mixed).

    ```rust
    let pool = Pool::new(16 * 1024);
    ```

- Intern a string slice in the `Pool`:

    ```rust
    let foo = "foo";
    let foo_id = pool.intern(foo).unwrap();
    ```

    This stores the string slice's copy in the `Pool`'s internal memory and returns an `ID` - an opaque POD type.
    `ID`'s may be compared. Equal strings have equal `ID`'s, and vice versa (as long as both `ID`'s are valid and were returned by the same `Pool`).

    Comparing `ID`'s returned by different `Pool`'s is undefined.
    Using `ID`'s returned by different `Pool`'s in calls to `Pool::lookup()`, `Pool::remove()` is undefined.

- Interning the same string again returns the same `ID` and increments the internal ref counter for this string:

    ```rust
    // `foo` and `foo_id` from above

    let other_foo_id = pool.intern(foo).unwrap();
    assert_eq!(foo_id, other_foo_id);
    ```

- Look up the interned string in the `Pool`:

    ```rust
    let foo = pool.lookup(foo_id).unwrap();
    assert_eq!(foo, "foo");

    let other_foo = pool.lookup(other_foo_id).unwrap();
    assert_eq!(other_foo, "foo");
    ```

- Remove the string from the `Pool`:

    ```rust
    pool.remove(foo_id).unwrap();

    // Still referenced by `other_foo_id` (which is equal to `foo_id`)
    assert!(pool.lookup(foo_id).is_ok());
    assert!(pool.lookup(other_foo_id).is_ok());

    pool.remove(other_foo_id).unwrap();

    // Now it's actually removed from the pool.
    assert!(pool.lookup(foo_id).is_err());
    assert!(pool.lookup(other_foo_id).is_err());
    ```

    If the same string was `intern()`'ed more than once in the `Pool`, it will need to be `remove()`'ed a matching number of times.

    The `ID` of a now-removed string is guaranteed to never be returned again by a call to `Pool::intern()` (at least until a large number (~4 billion) of unique strings are interned in the `Pool` and the underlying generation counter overflows; as well as the interned string is exactly the same *or* happens to hash to the same value - but this is an implementation detail).

## **Multithreaded use**

Singlethreaded use - simple:
- intern with `intern()`,
- lookup with `lookup()`,
- remove with `remove()`.

Looked up strings may be invalidated on `remove()` if the internal string storage happens to be defragmented (see implementation details). Rust borrow rules ensure we don't hold on to them as `remove()` is a mutable method.

Multithreaded use - more complex.

First, you might want to wrap the `Pool` in a `Mutex` / `RwLock`.
However, in this case Rust forces the lifetime of the looked up string to be determined
by the lifetime of the `MutexGuard` / `RwLockGuard`, NOT the lifetime of the `Pool` itself -
which defeats the whole point of using one.

This is the purpose of `lookup_unsafe()` - an escape hatch which returns the string
as a raw pointer with no lifetime associated with it.

Second, as stated above, `remove()` may defragment the `Pool` in one thread while
another thread is holding on to a recently returned string, now pointing to gargbage.

This is the purpose of `remove_gc()` / `gc()` methods. `remove_gc()` does not defragment the `Pool` immediately, but `gc()` must be called later at a point when only one thread accesses the `Pool` and no other threads hold on to looked up strings.

- in any thread, obtain (write) lock, intern with `intern()`,
- in any thread, obtain (read) lock, lookup with `lookup_unsafe()`,
- in any thread, obtain (write) lock, remove with `remove_gc()`,
- in some (probably main) thread, when no looked up strings are held by other threads,
obtain (write) lock, garbage collect with `gc()`.

## **Implementation details**

When interned, the strings are hashed to a 32-bit unsigned integer (currently using FNV-1a).

The `Pool` has a lookup hash map from this hash to the string's state - its ref count and location in a string chunk.

Hash collisions are handled by allowing more than one string state to be associated with a hash.

Removed `ID`'s are invalidated by incrementing a global generation counter. Each string's state also stores the generation counter it was interned with; and the same value forms the second part of the returned `ID`. The counter is incremented each time a new unique string is interned in the `Pool`. By comparing the `ID`'s generation value to that stored for the interned string in calls to `lookup()`, `remove()` etc. the `Pool` determines if the `ID` is valid. The generation counter also allows the `Pool` to handle hash collisions gracefully by disambiguating the string states based on their generation value. The (small) downside is the potential generation counter overflow (it's a 32-bit integer currently).

Each string chunk has a lookup array, mapping the strings' stable indices within that chunk to their offsets and lengths within it. Holes in the array form a free list of lookup indices.

Interned strings themselves are stored contiguosly in the string chunks; in the first chunk with enough space to fit one. When the strings are removed from the `Pool`, empty holes form in the string chunks. Currently, this is handled by defragmenting / compacting the string chunks whenever they drop below 50% occupancy when a string is removed.
