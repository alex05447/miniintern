use super::hash::Hash;

pub(crate) type Generation = u32;

/// Opaque unique interned string identifier.
///
/// May be compared to identifiers of other strings [`interned`](crate::Pool::intern) in the same [`Pool`](crate::Pool).
///
/// ID equality means string equality.
/// If the ID's are not equal, so are the strings.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ID {
    pub(crate) hash: Hash,
    pub(crate) generation: Generation,
}

impl Default for ID {
    fn default() -> Self {
        // TODO - check for correctness.
        Self {
            hash: Hash::MAX,
            generation: Generation::MAX,
        }
    }
}
