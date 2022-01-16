use std::{
    cell::Cell,
    fmt::{Debug, Formatter, Result},
    pin::Pin,
    ptr,
};

use crate::{DisplayResolved, Gc, Interner, Trace, Tracer, Unboxed, Value};

#[derive(Clone, PartialEq, Eq)]
pub struct Pair<'gc> {
    car: Cell<Value<'gc>>,
    cdr: Cell<Value<'gc>>,
}

#[derive(Clone, Default, PartialEq, Eq)]
pub struct Vector<'gc> {
    values: im_rc::Vector<Value<'gc>>,
}

#[derive(Debug)]
pub struct Closure<'gc> {
    pub function: Gc<'gc, Function>,
    upvalues: Pin<Box<[Cell<Value<'gc>>]>>,
}

#[derive(Debug)]
pub struct Function {
    pub offset: usize,
    pub upvalues: Box<[u16]>,
    pub parameters: u16,
    pub registers: u16,
}

impl<'gc> Pair<'gc> {
    #[inline]
    pub fn new(car: impl Into<Value<'gc>>, cdr: impl Into<Value<'gc>>) -> Self {
        Self {
            car: Cell::new(car.into()),
            cdr: Cell::new(cdr.into()),
        }
    }

    #[inline]
    pub fn car(&self) -> Value<'gc> {
        self.car.get()
    }

    #[inline]
    pub fn replace_car(&self, val: Value<'gc>) -> Value<'gc> {
        self.car.replace(val)
    }

    #[inline]
    pub fn cdr(&self) -> Value<'gc> {
        self.cdr.get()
    }

    #[inline]
    pub fn replace_cdr(&self, val: Value<'gc>) -> Value<'gc> {
        self.cdr.replace(val)
    }
}

impl<'gc> Vector<'gc> {
    #[inline]
    pub fn new(values: impl ExactSizeIterator<Item = Value<'gc>>) -> Vector<'gc> {
        Self {
            values: values.collect(),
        }
    }
}

impl<'gc> Closure<'gc> {
    #[inline]
    pub fn upvalues(&self) -> &[Cell<Value<'gc>>] {
        &self.upvalues
    }
}

impl<'gc> From<Gc<'gc, Function>> for Closure<'gc> {
    #[inline(always)]
    fn from(function: Gc<'gc, Function>) -> Self {
        Self {
            function,
            upvalues: vec![Cell::new(Value::NIL); function.upvalues.len()]
                .into_boxed_slice()
                .into(),
        }
    }
}

impl Eq for Closure<'_> {}

impl PartialEq for Closure<'_> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self, other)
    }
}

impl Eq for Function {}

impl PartialEq for Function {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self, other)
    }
}

impl<'gc> DisplayResolved for Pair<'gc> {
    fn fmt_resolved(&self, fmt: &mut Formatter<'_>, interner: &Interner) -> Result {
        fmt.write_str("(")?;

        self.car().fmt_resolved(fmt, interner)?;

        if let Unboxed::Pair(next) = self.cdr().unbox() {
            fmt.write_str(" ")?;
            let mut pair = next;
            loop {
                pair.car().fmt_resolved(fmt, interner)?;

                match pair.cdr().unbox() {
                    Unboxed::Pair(next) => {
                        fmt.write_str(" ")?;
                        pair = next;
                    }

                    Unboxed::Nil => break,

                    _ => {
                        fmt.write_str(" . ")?;
                        pair.cdr().fmt_resolved(fmt, interner)?;
                        break;
                    }
                }
            }
        } else {
            fmt.write_str(" . ")?;
            self.cdr().fmt_resolved(fmt, interner)?;
        }

        fmt.write_str(")")?;
        Ok(())
    }
}

impl DisplayResolved for Vector<'_> {
    fn fmt_resolved(&self, fmt: &mut Formatter<'_>, interner: &Interner) -> Result {
        fmt.write_str("[")?;
        let mut values = self.values.iter();
        if let Some(value) = values.next() {
            value.fmt_resolved(fmt, interner)?;
            for value in values {
                fmt.write_str(" ")?;
                value.fmt_resolved(fmt, interner)?;
            }
        }
        fmt.write_str("]")?;
        Ok(())
    }
}

impl Debug for Pair<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result {
        fmt.debug_tuple("")
            .field(&self.car.get())
            .field(&self.cdr.get())
            .finish()
    }
}

impl Debug for Vector<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result {
        fmt.debug_list().entries(self.values.iter()).finish()
    }
}

unsafe impl Trace for Pair<'_> {
    fn trace(&self, tracer: &mut impl Tracer) {
        self.car.trace(tracer);
        self.cdr.trace(tracer);
    }
}

unsafe impl Trace for Vector<'_> {
    fn trace(&self, tracer: &mut impl Tracer) {
        for v in self.values.iter() {
            v.trace(tracer);
        }
    }
}

unsafe impl Trace for Closure<'_> {
    fn trace(&self, tracer: &mut impl Tracer) {
        self.function.trace(tracer);
        self.upvalues.trace(tracer);
    }
}

unsafe impl Trace for Function {
    fn trace(&self, _tracer: &mut impl Tracer) {}
}
