pub use slope_derive::Trace;

use std::ptr::NonNull;

use crate::gc::{Header, Tracer};

/// Implements object tracing as performed during the mark phase of garbage
/// collection. Objects will be traced recursively from the root until all
/// reachable objects have been marked. Unmarked objects will be deallocated in
/// the subsequent sweep phase.
///
/// # Safety
/// Failure to trace a `Managed` object that is directly or indirectly reachable
/// from this struct may deallocated those objects while still being referenced.
pub unsafe trait Trace {
    fn trace(&self, tracer: &mut impl Tracer);
}

unsafe impl Trace for NonNull<Header> {
    fn trace(&self, tracer: &mut impl Tracer) {
        tracer.mark(*self)
    }
}

macro_rules! trace_leaf {
    ( <$($g:ident),*> $($t:tt)* ) => {
        unsafe impl<$($g),*> Trace for $($t)* {
            fn trace(&self, _tracer: &mut impl Tracer) {}
        }
    };

    ( $( $t: ty ),* ) => {
        $( trace_leaf!(<> $t); )*
    };
}

mod impls {
    pub use super::*;

    mod primitives {
        pub use super::*;

        trace_leaf! {
            (),
            bool,
            char,
            f32,
            f64,
            i8,
            i16,
            i32,
            i64,
            isize,
            u8,
            u16,
            u32,
            u64,
            usize,
            str
        }

        trace_leaf!(<T> *const T);
        trace_leaf!(<T> *mut T);

        unsafe impl<T: Trace> Trace for [T] {
            fn trace(&self, tracer: &mut impl Tracer) {
                for t in &self[..] {
                    t.trace(tracer);
                }
            }
        }

        unsafe impl<T> Trace for &[T] {
            fn trace(&self, _tracer: &mut impl Tracer) {}
        }
    }

    mod boxed {
        pub use super::*;

        unsafe impl<T: Trace + ?Sized> Trace for std::boxed::Box<T> {
            fn trace(&self, tracer: &mut impl Tracer) {
                (**self).trace(tracer);
            }
        }

        unsafe impl<T: Trace + ?Sized> Trace for std::pin::Pin<std::boxed::Box<T>> {
            fn trace(&self, tracer: &mut impl Tracer) {
                (**self).trace(tracer);
            }
        }
    }

    mod cell {
        pub use super::*;

        unsafe impl<T: Copy + Trace + ?Sized> Trace for std::cell::Cell<T> {
            fn trace(&self, tracer: &mut impl Tracer) {
                self.get().trace(tracer);
            }
        }

        unsafe impl<T: Trace + ?Sized> Trace for std::cell::RefCell<T> {
            fn trace(&self, tracer: &mut impl Tracer) {
                self.borrow().trace(tracer);
            }
        }
    }

    mod collections {
        pub use super::*;

        unsafe impl<K: Trace, V: Trace> Trace for std::collections::BTreeMap<K, V> {
            fn trace(&self, tracer: &mut impl Tracer) {
                for (k, v) in self {
                    k.trace(tracer);
                    v.trace(tracer);
                }
            }
        }

        unsafe impl<K: Eq + std::hash::Hash + Trace, V: Trace> Trace for std::collections::HashMap<K, V> {
            fn trace(&self, tracer: &mut impl Tracer) {
                for (k, v) in self {
                    k.trace(tracer);
                    v.trace(tracer);
                }
            }
        }

        unsafe impl<T: Trace> Trace for std::collections::LinkedList<T> {
            fn trace(&self, tracer: &mut impl Tracer) {
                for t in self {
                    t.trace(tracer);
                }
            }
        }

        unsafe impl<T: Trace> Trace for std::collections::VecDeque<T> {
            fn trace(&self, tracer: &mut impl Tracer) {
                for t in self {
                    t.trace(tracer);
                }
            }
        }
    }

    mod vec {
        pub use super::*;
        unsafe impl<T: Trace> Trace for Vec<T> {
            fn trace(&self, tracer: &mut impl Tracer) {
                for t in self {
                    t.trace(tracer);
                }
            }
        }

        unsafe impl<T: Trace + Clone> Trace for im_rc::Vector<T> {
            fn trace(&self, tracer: &mut impl Tracer) {
                for t in self {
                    t.trace(tracer);
                }
            }
        }
    }

    mod string {
        pub use super::*;
        trace_leaf!(String);
    }

    mod option {
        pub use super::*;

        unsafe impl<T: Trace> Trace for Option<T> {
            fn trace(&self, tracer: &mut impl Tracer) {
                for t in self {
                    t.trace(tracer);
                }
            }
        }
    }

    mod path {
        pub use super::*;
        trace_leaf! {
            std::path::Path,
            std::path::PathBuf
        }
    }

    mod rc {
        pub use super::*;
        trace_leaf!(<T> std::rc::Rc<T>);
        trace_leaf!(<T> std::rc::Weak<T>);
    }

    mod result {
        pub use super::*;

        unsafe impl<T: Trace, U: Trace> Trace for Result<T, U> {
            fn trace(&self, tracer: &mut impl Tracer) {
                match *self {
                    Ok(ref t) => t.trace(tracer),
                    Err(ref u) => u.trace(tracer),
                }
            }
        }
    }

    mod iter {
        pub use super::*;
        trace_leaf!(<T> std::slice::Iter<'_, T>);
        trace_leaf!(<T> std::iter::Skip<T>);
    }

    mod marker {
        pub use super::*;
        trace_leaf!(<T> std::marker::PhantomData<T>);
    }
}
