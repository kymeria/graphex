//! Graphex (**Grah** **Ex**plorer) is a small library helper to build command line
//! tool to explore (pseudo) graph.
//!
//! It mainly defines two traits ([Node] and [Display]) user have to implement for its
//! structs.
//!
//! - [Node] is for traversing the graph from node to node.
//! - [Display] is for display the final node at end of exploration.
//!
//! Few other strucs and functions are defined as helper.
//!
//! ## Features
//!
//! "Serde" support can be added using `serde` feature.
//! It add the `Node::serde` method to get a serde value from a [Node].
//!
//! To avoid any compilation error when a third party project activate the `serde` feature on
//! a project which has not implemented `Node::serde`, `Node::serde` returns a `Option` and a
//! default implementation returning `None` is provided.
//!
//! However, providing a default implementation prevent the compiler to fail if someone forget to
//! implement `Node::serde`. The feature `serde_no_defaul_impl` do not provide a default
//! implementation and so compiler fails if `Node::serde` is not implemented.
//!
//! !! `serde_no_default_impl` MUST NOT be activated in `Cargo.toml`. Activate it only temporarly
//! from command line `cargo build --features=serde_no_default_impl` !

mod display;
mod error;
mod explore;

pub use error::{Error, Result};

pub use display::*;
pub use explore::*;
