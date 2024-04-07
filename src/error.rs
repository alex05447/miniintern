use std::{
    error::Error as StdError,
    fmt::{Display, Formatter},
};

/// An error returned by the [`Pool`](crate::Pool).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Error {
    /// `ID` was invalid.
    InvalidStringID,
    /// String reference counter overflowed.
    /// Contains the maximum number of string copies the [`Pool`](crate::Pool) may intern.
    RefCountOverflow(usize),
    /// String counter overflowed.
    /// Contains the maximum number of unique strings the [`Pool`](crate::Pool) may intern.
    StringCountOverflow(usize),
}

impl StdError for Error {}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        use Error::*;

        match self {
            InvalidStringID => "string id was invalid".fmt(f),
            RefCountOverflow(max_num_copies) => write!(
                f,
                "string reference counter overflowed (max value is {})",
                max_num_copies
            ),
            StringCountOverflow(max_num_strings) => write!(
                f,
                "string counter overflowed (max value is {})",
                max_num_strings
            ),
        }
    }
}
