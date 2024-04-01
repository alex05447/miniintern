pub(crate) type Hash = u32;

pub(crate) fn string_hash_fnv1a(string: &str) -> Hash {
    const FNV_PRIME: Hash = 16777619;
    const FNV_OFFSET: Hash = 2166136261;

    let mut hash = FNV_OFFSET;

    for byte in string.bytes() {
        hash ^= byte as Hash;
        hash = hash.overflowing_mul(FNV_PRIME).0;
    }

    hash
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash() {
        assert_eq!(string_hash_fnv1a("foo"), 2851307223);
        assert_eq!(string_hash_fnv1a("bar"), 1991736602);
    }

    #[test]
    fn fnv1a_hash_collisions() {
        // https://softwareengineering.stackexchange.com/questions/49550/which-hashing-algorithm-is-best-for-uniqueness-and-speed

        assert_eq!(string_hash_fnv1a("costarring"), string_hash_fnv1a("liquid"),);

        assert_eq!(
            string_hash_fnv1a("declinate"),
            string_hash_fnv1a("macallums"),
        );

        assert_eq!(string_hash_fnv1a("altarage"), string_hash_fnv1a("zinke"),);

        assert_eq!(string_hash_fnv1a("altarages"), string_hash_fnv1a("zinkes"),);

        assert_ne!(string_hash_fnv1a("foo"), string_hash_fnv1a("bar"),);
    }
}
