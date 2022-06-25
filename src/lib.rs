//! # miniintern
//!
//! A minimalistic Rust string interning / pooling library.
//!
//! Originally written for `miniecs` string support in component data.

mod chunk;
mod error;
mod hash;
mod id;
mod pool;

pub use {chunk::*, error::*, id::*, pool::*};

pub(crate) use hash::*;
