//! # miniintern
//!
//! Minimalistic string interning / string pool library written in Rust.
//!
//! Originally written for `miniecs` string support in component data.

mod error;
mod hash;
mod string_chunk;
mod string_id;
mod string_pool;

pub use {error::Error, string_chunk::ChunkSize, string_id::StringID, string_pool::{StringPool, UnsafeStr}};
