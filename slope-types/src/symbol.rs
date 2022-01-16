use lasso::{Key, Rodeo};

use std::{
    convert::TryInto,
    fmt::{Formatter, Result},
};

use crate::DisplayResolved;

pub struct Interner {
    inner: Rodeo<Symbol>,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Symbol(u32);

impl Interner {
    #[inline]
    pub fn get(&mut self, str: impl AsRef<str>) -> Option<Symbol> {
        self.inner.get(str)
    }

    #[inline]
    pub fn intern(&mut self, str: impl AsRef<str>) -> Symbol {
        self.inner.get_or_intern(str)
    }

    #[inline]
    pub fn intern_static(&mut self, str: &'static str) -> Symbol {
        self.inner.get_or_intern_static(str)
    }

    #[inline]
    pub fn resolve(&self, symbol: &Symbol) -> &str {
        self.inner.resolve(symbol)
    }
}

impl Default for Interner {
    #[inline]
    fn default() -> Self {
        Self {
            inner: Rodeo::new(),
        }
    }
}

impl Symbol {
    #[inline]
    pub(crate) const unsafe fn from_u32(idx: u32) -> Self {
        Symbol(idx)
    }

    #[inline]
    pub(crate) const fn as_u32(&self) -> u32 {
        self.0
    }
}

unsafe impl Key for Symbol {
    #[inline]
    unsafe fn into_usize(self) -> usize {
        self.0 as usize
    }

    #[inline]
    fn try_from_usize(idx: usize) -> Option<Self> {
        Some(Self(idx.try_into().ok()?))
    }
}

impl DisplayResolved for Symbol {
    fn fmt_resolved(&self, fmt: &mut Formatter<'_>, interner: &Interner) -> Result {
        write!(fmt, "{}", interner.resolve(&self))?;
        Ok(())
    }
}
