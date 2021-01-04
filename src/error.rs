use {
    super::string_chunk::ChunkSize,
    std::{
        error::Error as StdError,
        fmt::{Display, Formatter},
    },
};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Error {
    /// Attempted to [`intern`] an empty (zero-length) string.
    /// [`intern`]: struct.StringPool.html#method.intern
    EmptyString,
    /// Attempted to [`intern`] a string whose length in bytes is greater
    /// then the maximum length supported by the [`string pool`]
    /// (as determinded by the `chunk_size` parameter minus (small) chunk header overhead).
    /// [`string pool`]: struct.StringPool.html
    /// [`intern`]: struct.StringPool.html#method.intern
    StringTooLong {
        /// The length of the string in bytes.
        string_length: usize,
        /// Maximum string length in bytes which may be stored by the [`string pool`].
        /// [`string pool`]: struct.StringPool.html
        max_string_length: ChunkSize,
    },
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

        match self{
            EmptyString => "attempted to intern an empty (zero-length) string".fmt(f),
            StringTooLong { string_length, max_string_length} => write!(
                f, "attempted to intern a string whose length in bytes ({}b) exceeds the maximum supported value ({}b)",
                string_length,
                max_string_length
            ),
            InvalidStringID => "string id was invalid".fmt(f),
            RefCountOverflow(max_num_copies) => write!(f, "string reference counter overflowed (max value is {})", max_num_copies),
        }
    }
}
