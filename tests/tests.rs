use miniintern::*;

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
    //assert_eq!(asdf_id.0, string_hash(asdf));
    assert_eq!(asdf_id, StringPool::string_id(asdf).unwrap());

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

    let gh_id = StringPool::string_id(gh).unwrap();
    //assert_eq!(gh_id.0, string_hash(gh));

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
    assert!(pool.remove_gc(asdf_id).is_err());
    assert!(pool.remove(asdf_id).is_err());

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
    assert!(pool.remove_gc(gh_id).is_err());
    assert!(pool.remove(gh_id).is_err());

    assert!(pool.lookup(gh_id).is_none());

    assert_eq!(pool.lookup(long_string_id).unwrap(), long_string);

    // Should free the last chunk.
    pool.remove(long_string_id).unwrap();
    assert!(pool.remove_gc(long_string_id).is_err());
    assert!(pool.remove(long_string_id).is_err());

    // String is too long.
    let very_long_string = "asdfghjkl";
    assert_eq!(
        pool.intern(very_long_string).unwrap_err(),
        StringPoolError::StringTooLong(8)
    );
}
