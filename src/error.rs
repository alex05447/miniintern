use std::{
    error::Error as StdError,
    fmt::{Display, Formatter},
};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Error {
    /// Attempted to [`intern`] an empty (zero-length) string.
    /// [`intern`]: struct.StringPool.html#method.intern
    EmptyString,
    /// `StringID` was invalid.
    InvalidStringID,
    /// String reference counter overflowed.
    /// Contains the maximum number of string copies the [`string pool`] may intern.
    /// [`string pool`]: struct.StringPool.html
    RefCountOverflow(usize),
}

impl StdError for Error {}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        use Error::*;

        match self {
            EmptyString => "attempted to intern an empty (zero-length) string".fmt(f),
            InvalidStringID => "string id was invalid".fmt(f),
            RefCountOverflow(max_num_copies) => write!(
                f,
                "string reference counter overflowed (max value is {})",
                max_num_copies
            ),
        }
    }
}
