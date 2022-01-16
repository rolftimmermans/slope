#[macro_use]
mod macros;

mod assemble;
mod compile;
mod expr;
mod form;
mod syntax;
mod vm;

use ahash::{AHashMap as HashMap, AHashSet as HashSet};
use indexmap::IndexSet;

pub use slope_parse::ByteRange;
pub use slope_types::Value;
pub use vm::{Error, VirtualMachine};
