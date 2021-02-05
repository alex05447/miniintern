use super::hash::StringHash;

pub(crate) type StringGeneration = u32;

/// Unique interned string identifier.
///
/// May be compared to identifiers of other strings interned in the same [`string pool`].
///
/// ID equality means string equality.
/// If the ID's are not equal, so are the strings.
///
/// [`string pool`]: struct.StringPool.html
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct StringID {
    pub(crate) string_hash: StringHash,
    pub(crate) generation: StringGeneration,
}

impl Default for StringID {
    fn default() -> Self {
        // TODO - check for correctness.
        Self {
            string_hash: StringHash::MAX,
            generation: StringGeneration::MAX,
        }
    }
}
