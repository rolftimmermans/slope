mod gc;
mod object;
mod symbol;
mod trace;
mod value;

pub use gc::{
    AllocationContext, Gc, Heap, Managed, MutationContext, ObjectKind, Parameters, Root, Tracer,
};
pub use object::{Closure, Function, Pair, Vector};
pub use symbol::{Interner, Symbol};
pub use trace::Trace;
pub use value::{DeepEq, DisplayResolved, Unboxed, Value};

#[macro_export]
macro_rules! assert_deep_eq {
    ($a:expr, $b:expr) => {
        assert!($crate::DeepEq::deep_eq(&$a, &$b));
    };

    ($a:expr, $b:expr, $($arg:tt)+) => {
        assert!($crate::DeepEq::deep_eq(&$a, &$b), $($arg)+);
    };
}
