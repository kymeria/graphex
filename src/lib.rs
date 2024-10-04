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

mod display;
mod error;
mod explore;

pub use error::{Error, Result};

pub use display::*;
pub use explore::*;
