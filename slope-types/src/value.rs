use std::{
    char,
    cmp::Ordering,
    fmt::{Debug, Display, Formatter, Result},
    marker::PhantomData,
    ops::{Add, Div, Mul, Rem, Sub},
    ptr::NonNull,
};

use crate::{
    gc::{data_to_header, header_to_data, Header, Managed},
    Closure, Function, Gc, Interner, ObjectKind, Pair, Symbol, Trace, Tracer, Vector,
};

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Value<'gc> {
    bits: u64,
    _marker: PhantomData<Gc<'gc, String>>,
}

#[derive(Copy, Clone, PartialEq)]
pub enum Unboxed<'gc> {
    Nil,
    Bool(bool),
    Char(char),
    Symbol(Symbol),
    Number(f64),
    String(Gc<'gc, String>),
    Pair(Gc<'gc, Pair<'gc>>),
    Vector(Gc<'gc, Vector<'gc>>),
    Closure(Gc<'gc, Closure<'gc>>),
    Function(Gc<'gc, Function>),
}

pub trait DeepEq {
    fn deep_eq(&self, other: &Self) -> bool;
}

pub trait DisplayResolved {
    fn fmt_resolved(&self, fmt: &mut Formatter<'_>, interner: &Interner) -> Result;
}

const QUIET_NAN: u64 = 0x7ffc000000000000;

const NIL: u64 = 1 as u64 | QUIET_NAN;
const BOOL_FLAG: u64 = 0x0000100000000000 | QUIET_NAN;
const CHAR_FLAG: u64 = 0x0000200000000000 | QUIET_NAN;
const SYM_FLAG: u64 = 0x0000400000000000 | QUIET_NAN;
const PTR_FLAG: u64 = 0x8000000000000000 | QUIET_NAN;

const VALUE_MASK: u64 = BOOL_FLAG | CHAR_FLAG | SYM_FLAG | PTR_FLAG;

const ZERO_VAL: u64 = 0 as u64;

macro_rules! cast_object {
    ( $ptr:expr; $( $ki:ident, )+ ) => {
        match $ptr.cast::<Header>().as_ref().kind() {
            $(
                ObjectKind::$ki => {
                    Unboxed::$ki(Gc::from_ptr(header_to_data::<$ki>($ptr)))
                }
            )+

            ObjectKind::Blank => Unboxed::Nil,
        }
    };
}

impl<'gc> Value<'gc> {
    pub const NIL: Value<'gc> = Value {
        bits: NIL,
        _marker: PhantomData,
    };

    pub const ZERO: Value<'gc> = Value {
        bits: ZERO_VAL,
        _marker: PhantomData,
    };

    pub const TRUE: Value<'gc> = Value {
        bits: true as u64 | BOOL_FLAG,
        _marker: PhantomData,
    };

    pub const FALSE: Value<'gc> = Value {
        bits: false as u64 | BOOL_FLAG,
        _marker: PhantomData,
    };

    #[inline]
    pub const fn is_false(&self) -> bool {
        self.bits == false as u64 | BOOL_FLAG
    }

    #[inline]
    pub const fn is_nil(&self) -> bool {
        self.bits == NIL
    }

    #[inline]
    pub const fn is_bool(&self) -> bool {
        self.bits & VALUE_MASK == BOOL_FLAG
    }

    #[inline]
    pub const fn is_char(&self) -> bool {
        self.bits & VALUE_MASK == CHAR_FLAG
    }

    #[inline]
    pub const fn is_symbol(&self) -> bool {
        self.bits & VALUE_MASK == SYM_FLAG
    }

    #[inline]
    pub const fn is_number(&self) -> bool {
        self.bits & QUIET_NAN != QUIET_NAN
    }

    #[inline]
    pub const fn is_object(&self) -> bool {
        self.bits & PTR_FLAG == PTR_FLAG
    }

    #[inline]
    pub const fn as_bits(&self) -> i64 {
        self.bits as i64
    }

    #[inline(always)]
    pub fn unbox(&self) -> Unboxed<'gc> {
        match self.bits & VALUE_MASK {
            BOOL_FLAG => Unboxed::Bool(self.bits == 1 | BOOL_FLAG),

            CHAR_FLAG => {
                Unboxed::Char(unsafe { char::from_u32_unchecked((self.bits & !CHAR_FLAG) as u32) })
            }

            SYM_FLAG => {
                Unboxed::Symbol(unsafe { Symbol::from_u32((self.bits & !SYM_FLAG) as u32) })
            }

            _ if self.bits == NIL => Unboxed::Nil,

            _ if self.bits & PTR_FLAG == PTR_FLAG => unsafe {
                let ptr = self.as_ptr();
                cast_object! {
                    ptr;
                    String,
                    Pair,
                    Vector,
                    Closure,
                    Function,
                }
            },

            _ if self.bits & QUIET_NAN != QUIET_NAN => Unboxed::Number(f64::from_bits(self.bits)),

            _ => panic!("invalid value"),
        }
    }

    #[inline]
    unsafe fn as_ptr(&self) -> NonNull<Header> {
        debug_assert!(self.is_object());
        NonNull::new_unchecked((self.bits & !PTR_FLAG) as *mut _)
    }
}

unsafe impl Trace for Value<'_> {
    fn trace(&self, tracer: &mut impl Tracer) {
        if self.is_object() {
            tracer.mark(unsafe { self.as_ptr() });
        }
    }
}

impl<'gc> From<()> for Value<'gc> {
    #[inline]
    fn from(_: ()) -> Self {
        Value::NIL
    }
}

impl<'gc> From<bool> for Value<'gc> {
    #[inline]
    fn from(value: bool) -> Self {
        Self {
            bits: value as u64 | BOOL_FLAG,
            _marker: PhantomData,
        }
    }
}

impl<'gc> From<char> for Value<'gc> {
    #[inline]
    fn from(value: char) -> Self {
        Self {
            bits: value as u64 | CHAR_FLAG,
            _marker: PhantomData,
        }
    }
}

impl<'gc> From<Symbol> for Value<'gc> {
    #[inline]
    fn from(value: Symbol) -> Self {
        Self {
            bits: value.as_u32() as u64 | SYM_FLAG,
            _marker: PhantomData,
        }
    }
}

impl<'gc> From<f64> for Value<'gc> {
    #[inline]
    fn from(number: f64) -> Self {
        debug_assert!(number.to_bits() & QUIET_NAN != QUIET_NAN);
        Self {
            bits: number.to_bits(),
            _marker: PhantomData,
        }
    }
}

impl<'gc> From<u64> for Value<'gc> {
    #[inline]
    fn from(number: u64) -> Self {
        Self {
            bits: (number as f64).to_bits(),
            _marker: PhantomData,
        }
    }
}

impl<'gc, T: Managed> From<Gc<'gc, T>> for Value<'gc> {
    #[inline]
    fn from(value: Gc<'gc, T>) -> Self {
        Self {
            bits: unsafe { data_to_header(value.as_ptr()) }.as_ptr() as u64 | PTR_FLAG,
            _marker: PhantomData,
        }
    }
}

impl<'gc, T: Into<Value<'gc>> + Copy> From<&T> for Value<'gc> {
    #[inline]
    fn from(value: &T) -> Self {
        (*value).into()
    }
}

impl DeepEq for Value<'_> {
    #[inline]
    fn deep_eq(&self, other: &Self) -> bool {
        self.unbox() == other.unbox()
    }
}

impl PartialOrd for Value<'_> {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self.unbox(), other.unbox()) {
            (Unboxed::Nil, Unboxed::Nil) => Some(Ordering::Equal),
            (Unboxed::Char(a), Unboxed::Char(b)) => a.partial_cmp(&b),
            (Unboxed::Number(a), Unboxed::Number(b)) => a.partial_cmp(&b),
            (Unboxed::Pair(..), Unboxed::Pair(..)) => None,
            (Unboxed::Symbol(..), Unboxed::Symbol(..)) => None,
            (Unboxed::String(a), Unboxed::String(b)) => a.partial_cmp(&*b),
            (..) => None,
        }
    }
}

macro_rules! impl_op {
    ($trait:ident, $method:ident) => {
        impl<'gc> $trait for &Value<'gc> {
            type Output = Value<'gc>;

            #[inline]
            fn $method(self, rhs: Self) -> Self::Output {
                let val = f64::from_bits(self.bits).$method(f64::from_bits(rhs.bits));
                debug_assert!(val.to_bits() == f64::NAN.to_bits() || !val.is_nan());
                val.into()
            }
        }
    };
}

impl_op!(Add, add);
impl_op!(Sub, sub);
impl_op!(Mul, mul);
impl_op!(Div, div);
impl_op!(Rem, rem);

impl Debug for Value<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result {
        match self.unbox() {
            Unboxed::Nil => write!(fmt, "nil"),
            Unboxed::Bool(bool) => {
                if bool {
                    write!(fmt, "#t")
                } else {
                    write!(fmt, "#f")
                }
            }
            Unboxed::Char(char) => write!(fmt, "'{}'", char),
            Unboxed::Symbol(symbol) => write!(fmt, "{:?}", symbol),
            Unboxed::Number(number) => write!(fmt, "{}", number),
            Unboxed::String(string) => write!(fmt, "{:?}", string),
            Unboxed::Pair(pair) => write!(fmt, "{:?}", pair),
            Unboxed::Vector(vector) => write!(fmt, "{:?}", vector),
            Unboxed::Closure(closure) => write!(fmt, "{:?}", closure),
            Unboxed::Function(function) => write!(fmt, "{:?}", function),
        }
    }
}

impl<T> DisplayResolved for T
where
    T: Display,
{
    fn fmt_resolved(&self, fmt: &mut Formatter<'_>, _interner: &Interner) -> Result {
        self.fmt(fmt)
    }
}

impl DisplayResolved for Value<'_> {
    fn fmt_resolved(&self, fmt: &mut Formatter<'_>, interner: &Interner) -> Result {
        match self.unbox() {
            Unboxed::Nil => write!(fmt, "nil"),
            Unboxed::Bool(bool) => {
                if bool {
                    write!(fmt, "#t")
                } else {
                    write!(fmt, "#f")
                }
            }
            Unboxed::Char(char) => write!(fmt, "'{}'", char),
            Unboxed::Symbol(symbol) => symbol.fmt_resolved(fmt, interner),
            Unboxed::Number(number) => number.fmt_resolved(fmt, interner),
            Unboxed::String(string) => write!(fmt, "{:?}", string),
            Unboxed::Pair(pair) => pair.fmt_resolved(fmt, interner),
            Unboxed::Vector(vector) => vector.fmt_resolved(fmt, interner),
            Unboxed::Closure(_) => write!(fmt, "(closure)"),
            Unboxed::Function(_) => write!(fmt, "(func)"),
        }
    }
}

impl Display for Unboxed<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result {
        match self {
            Unboxed::Nil => write!(fmt, "nil"),
            Unboxed::Bool(_) => write!(fmt, "boolean"),
            Unboxed::Char(_) => write!(fmt, "character"),
            Unboxed::Symbol(_) => write!(fmt, "symbol"),
            Unboxed::Number(_) => write!(fmt, "number"),
            Unboxed::String(_) => write!(fmt, "string"),
            Unboxed::Pair(_) => write!(fmt, "pair"),
            Unboxed::Vector(_) => write!(fmt, "vector"),
            Unboxed::Closure(_) => write!(fmt, "closure"),
            Unboxed::Function(_) => write!(fmt, "function"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck_macros::quickcheck;
    use std::{f64::consts::PI, panic::catch_unwind};

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct Test<T: Clone + Debug + Trace + 'static>(T);

    unsafe impl<T: Clone + Debug + Trace + 'static> Trace for Test<T> {
        fn trace(&self, tracer: &mut impl Tracer) {
            self.0.trace(tracer);
        }
    }

    impl<T: Clone + Debug + Trace + 'static> Display for Test<T> {
        fn fmt(&self, fmt: &mut Formatter<'_>) -> Result {
            Debug::fmt(self, fmt)
        }
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    fn nil_type(_inner: ()) -> bool {
        let value = Value::NIL;
        value.is_nil() && !value.is_false()
    }

    #[test]
    fn nil_debug() {
        assert_eq!("nil", format!("{:?}", Value::NIL));
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    fn bool_roundtrip(inner: bool) -> bool {
        Unboxed::Bool(inner) == Value::from(inner).unbox()
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    fn bool_kind(inner: bool) -> bool {
        let value = Value::from(inner);
        value.is_bool() && value.is_false() == !inner
    }

    #[test]
    fn bool_debug() {
        assert_eq!("#t", format!("{:?}", Value::TRUE));
        assert_eq!("#f", format!("{:?}", Value::FALSE));
    }

    #[test]
    fn bool_eq() {
        assert!(Value::TRUE != Value::FALSE);
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    fn number_flt_roundtrip(inner: f64) -> bool {
        Unboxed::Number(inner) == Value::from(inner).unbox()
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    fn number_int_roundtrip(inner: u64) -> bool {
        Unboxed::Number(inner as f64) == Value::from(inner).unbox()
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    fn number_kind(inner: f64) -> bool {
        let value = Value::from(inner);
        value.is_number() && !value.is_false()
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    fn number_nan_kind(_inner: ()) -> bool {
        let value = Value::from(f64::NAN);
        value.is_number() && !value.is_false()
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    fn number_infinity_kind(_inner: ()) -> bool {
        let value = Value::from(f64::INFINITY);
        value.is_number() && !value.is_false()
    }

    #[test]
    fn number_debug() {
        assert_eq!("3.141592653589793", format!("{:?}", Value::from(PI)));
        assert_eq!("NaN", format!("{:?}", Value::from(f64::NAN)));
        assert_eq!("inf", format!("{:?}", Value::from(f64::INFINITY)));
    }

    #[test]
    fn number_eq() {
        assert!(Value::from(1.5) == Value::from(1.5));
        assert!(Value::from(-3.7) == Value::from(-3.7));
        assert!(Value::from(f64::NAN) == Value::from(f64::NAN));
        assert!(Value::from(0.0) != Value::from(9.5));
        assert!(Value::from(3.7) != Value::from(-3.7));
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    fn char_roundtrip(inner: char) -> bool {
        Unboxed::Char(inner) == Value::from(inner).unbox()
    }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    fn char_kind(inner: char) -> bool {
        let value = Value::from(inner);
        value.is_char() && !value.is_false()
    }

    #[test]
    fn char_debug() {
        assert_eq!("'c'", format!("{:?}", Value::from('c')));
        assert_eq!("'λ'", format!("{:?}", Value::from('λ')));
    }

    #[test]
    fn char_eq() {
        assert!(Value::from('a') == Value::from('a'));
        assert!(Value::from('λ') == Value::from('λ'));
        assert!(Value::from('а') != Value::from('a')); // First is Cyrillic.
    }

    // #[test]
    // fn pair_roundtrip() {
    //     let value = Value::from((1.0.into(), 2.0.into()));
    //     collect::collect_cycles();
    //     if let Unwrapped::Pair(value) = value.unwrap() {
    //         assert_eq!(&Value::from(1.0), value.as_ref().car());
    //     } else {
    //         assert!(false);
    //     }
    // }

    // #[test]
    // fn pair_kind() {
    //     let value = Value::from((1.0.into(), 2.0.into()));
    //     collect::collect_cycles();
    //     assert!(value.is_object());
    //     assert!(value.is_pair());
    //     assert!(matches!(value.unwrap(), Unwrapped::Pair(..)));
    //     assert!(!value.is_false());
    // }

    // #[test]
    // fn pair_eq() {
    //     let a = Value::from((Value::NIL, Value::NIL));
    //     let b = Value::from((Value::NIL, Value::NIL));
    //     let c = Value::from((Value::FALSE, Value::NIL));
    //     assert!(a == a);
    //     assert!(a != b);
    //     assert!(a.deep_eq(&b));
    //     assert!(!a.deep_eq(&c));
    // }

    // #[test]
    // fn string_roundtrip() {
    //     let value = Value::from("foobar");
    //     collect::collect_cycles();
    //     if let Unwrapped::String(value) = value.unwrap() {
    //         assert_eq!("foobar", value.as_ref());
    //     } else {
    //         assert!(false);
    //     }
    // }

    // #[test]
    // fn string_kind() {
    //     let value = Value::from("foobar");
    //     collect::collect_cycles();
    //     assert!(value.is_object());
    //     assert!(value.is_string());
    //     assert!(matches!(value.unwrap(), Unwrapped::String(..)));
    //     assert!(!value.is_false());
    // }

    // #[test]
    // fn symbol_roundtrip() {
    //     let symbol = Symbol(Rc::new("foobar".into()));
    //     let value = Value::from(symbol.clone());
    //     collect::collect_cycles();
    //     if let Unwrapped::Symbol(value) = value.unwrap() {
    //         assert_eq!(&symbol, value.as_ref());
    //     } else {
    //         assert!(false);
    //     }
    // }

    // #[test]
    // fn symbol_kind() {
    //     let symbol = Symbol(Rc::new("foobar".into()));
    //     let value = Value::from(symbol);
    //     collect::collect_cycles();
    //     assert!(value.is_object());
    //     assert!(value.is_symbol());
    //     assert!(matches!(value.unwrap(), Unwrapped::Symbol(..)));
    //     assert!(!value.is_false());
    // }

    // #[test]
    // fn symbol_eq() {
    //     let mut int1 = Interner::default();
    //     let mut int2 = Interner::default();
    //     let a1 = Value::from(int1.intern("foo"));
    //     let b1 = Value::from(int1.intern("foo"));
    //     let a2 = Value::from(int2.intern("foo"));
    //     let b2 = Value::from(int2.intern("foo"));
    //     assert!(a1 == a1);
    //     assert!(a1 == b1);
    //     assert!(a2 == a2);
    //     assert!(b2 == b2);
    //     assert!(a1 != a2);
    //     assert!(a1 != b2);
    //     assert!(!a1.deep_eq(&a2));
    //     assert!(!a1.deep_eq(&b2));
    // }

    // #[test]
    // fn wrapped_roundtrip() {
    //     let data = Test(vec!["hi".to_owned()]);
    //     let value = Value::wrap(data.clone());
    //     collect::collect_cycles();
    //     if let Unwrapped::Wrapped(value) = value.unwrap() {
    //         assert_eq!(Some(&data), value.as_ref().downcast::<Test<Vec<String>>>());
    //     } else {
    //         assert!(false);
    //     }
    // }

    // #[test]
    // fn wrapped_kind() {
    //     let data = Test(vec!["hi".to_owned()]);
    //     let value = Value::wrap(data);
    //     collect::collect_cycles();
    //     assert!(value.is_object());
    //     assert!(value.is_wrapped());
    //     assert!(matches!(value.unwrap(), Unwrapped::Wrapped(..)));
    //     assert!(!value.is_false());
    // }

    #[quickcheck]
    #[cfg_attr(miri, ignore)]
    fn mutually_exclusive_kind(bits: u64) -> bool {
        let value1 = Value {
            bits,
            _marker: PhantomData,
        };

        let value2 = Value {
            bits: bits | QUIET_NAN,
            _marker: PhantomData,
        };

        let value3 = Value {
            bits: bits | f64::NAN.to_bits(),
            _marker: PhantomData,
        };

        [value1, value2, value3].iter().all(|value| {
            if value.is_object() {
                !value.is_nil()
                    && !value.is_bool()
                    && !value.is_char()
                    && !value.is_symbol()
                    && !value.is_number()
            } else {
                catch_unwind(move || match value.unbox() {
                    Unboxed::Nil => {
                        value.is_nil()
                            && !value.is_bool()
                            && !value.is_char()
                            && !value.is_symbol()
                            && !value.is_number()
                    }
                    Unboxed::Bool(_) => {
                        !value.is_nil()
                            && value.is_bool()
                            && !value.is_char()
                            && !value.is_symbol()
                            && !value.is_number()
                    }
                    Unboxed::Char(_) => {
                        !value.is_nil()
                            && !value.is_bool()
                            && value.is_char()
                            && !value.is_symbol()
                            && !value.is_number()
                    }
                    Unboxed::Symbol(_) => {
                        !value.is_nil()
                            && !value.is_bool()
                            && !value.is_char()
                            && value.is_symbol()
                            && !value.is_number()
                    }
                    Unboxed::Number(_) => {
                        !value.is_nil()
                            && !value.is_bool()
                            && !value.is_char()
                            && !value.is_symbol()
                            && value.is_number()
                    }
                    _ => unreachable!(),
                })
                .unwrap_or(true)
            }
        })
    }
}
