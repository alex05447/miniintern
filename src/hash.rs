pub(crate) type StringHash = u32;

pub(crate) fn fnv1a32(string: &str) -> StringHash {
    const FNV_PRIME: StringHash = 16777619;
    const FNV_OFFSET: StringHash = 2166136261;

    let mut hash = FNV_OFFSET;

    for byte in string.bytes() {
        hash = hash ^ byte as StringHash;
        hash = hash.overflowing_mul(FNV_PRIME).0;
    }

    hash
}

#[cfg(test)]
mod tests {
    #[test]
    fn fnv1a32() {
        assert_eq!(super::fnv1a32("foo"), 2851307223);
        assert_eq!(super::fnv1a32("bar"), 1991736602);
    }
}
