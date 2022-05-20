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

pub(crate) fn debug_unreachable() -> ! {
    if cfg!(debug_assertions) {
        unreachable!()
    } else {
        unsafe { std::hint::unreachable_unchecked() }
    }
}
