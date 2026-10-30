//! Exercises `-split-files`: one Lean module per Rust module, with modules that
//! form a dependency SCC merged into one, and modules that alternate
//! opaque/transparent declarations split into chains of files.
#![feature(register_tool)]
#![register_tool(verify)]

pub mod external;
pub mod layered;
pub mod nested;
pub mod ops;
pub mod ping;
pub mod pong;
#[path = "path_target.rs"]
pub mod renamed;
pub mod scoped;
pub mod types;
pub mod uses_layered;
pub mod viamacro;
