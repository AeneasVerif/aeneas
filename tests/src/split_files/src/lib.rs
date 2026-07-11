//! Exercises `-split-files`: one Lean module per source file, with files that
//! form a dependency SCC merged into one module, and modules that alternate
//! opaque/transparent declarations split into chains of files.
#![feature(register_tool)]
#![register_tool(verify)]

pub mod layered;
pub mod ops;
pub mod ping;
pub mod pong;
pub mod types;
