use slope_parse::Atom;

use slope_types::{DeepEq, Pair, Trace, Unboxed, Value};

use std::{
    cell::Cell,
    fmt::{self, Debug, Display, Formatter},
    mem::take,
};

use crate::vm::AllocationContext;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Default)]
pub(crate) struct VariableId(pub(crate) u32);

impl Debug for VariableId {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "v{}", self.0)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Trace)]
#[repr(u8)]
pub enum UnaryOp {
    // List operators
    Car,
    Cdr,

    // Predicates
    IsNil,
    IsBool,
    IsChar,
    IsSymbol,
    IsNumber,
    IsString,
    IsPair,
    IsVector,
    IsClosure,
    IsFunction,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Trace)]
#[repr(u8)]
#[allow(dead_code)]
pub enum BinaryOp {
    // Comparison operators
    IsEq,
    IsGt,
    IsGtEq,
    IsLt,
    IsLtEq,

    // Mathematical operators
    Add,
    Mul,
    Sub,
    Div,
    Rem,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Trace)]
#[repr(u8)]
pub enum BuiltinFunc {
    Cons,
    List,
}

impl UnaryOp {
    #[inline(always)]
    pub(crate) fn apply<'gc>(&self, val: Value<'gc>) -> Value<'gc> {
        match self {
            UnaryOp::Car => {
                if let Unboxed::Pair(pair) = val.unbox() {
                    pair.car()
                } else {
                    panic!("not a list: {:?}", val);
                }
            }

            UnaryOp::Cdr => {
                if let Unboxed::Pair(pair) = val.unbox() {
                    pair.cdr()
                } else {
                    panic!("not a list: {:?}", val);
                }
            }

            UnaryOp::IsNil => matches!(val.unbox(), Unboxed::Nil).into(),

            UnaryOp::IsBool => matches!(val.unbox(), Unboxed::Bool(..)).into(),

            UnaryOp::IsChar => matches!(val.unbox(), Unboxed::Char(..)).into(),

            UnaryOp::IsSymbol => matches!(val.unbox(), Unboxed::Symbol(..)).into(),

            UnaryOp::IsNumber => matches!(val.unbox(), Unboxed::Number(..)).into(),

            UnaryOp::IsString => matches!(val.unbox(), Unboxed::String(..)).into(),

            UnaryOp::IsPair => matches!(val.unbox(), Unboxed::Pair(..)).into(),

            UnaryOp::IsVector => matches!(val.unbox(), Unboxed::Vector(..)).into(),

            UnaryOp::IsClosure => matches!(val.unbox(), Unboxed::Closure(..)).into(),

            UnaryOp::IsFunction => matches!(val.unbox(), Unboxed::Function(..)).into(),
        }
    }
}

impl BinaryOp {
    #[inline(always)]
    pub(crate) fn apply<'gc>(&self, val1: Value<'gc>, val2: Value<'gc>) -> Value<'gc> {
        match self {
            BinaryOp::IsEq => Value::from(val1 == val2),
            BinaryOp::IsGt => Value::from(val1 > val2),
            BinaryOp::IsGtEq => Value::from(val1 >= val2),
            BinaryOp::IsLt => Value::from(val1 < val2),
            BinaryOp::IsLtEq => Value::from(val1 <= val2),
            BinaryOp::Add => &val1 + &val2,
            BinaryOp::Mul => &val1 * &val2,
            BinaryOp::Sub => &val1 - &val2,
            BinaryOp::Div => &val1 / &val2,
            BinaryOp::Rem => &val1 % &val2,
        }
    }
}

impl BuiltinFunc {
    #[inline(always)]
    pub(crate) fn apply<'gc>(
        &self,
        ctx: &mut AllocationContext<'gc>,
        vals: &[Cell<Value<'gc>>],
    ) -> Value<'gc> {
        match self {
            BuiltinFunc::Cons => Value::from(ctx.alloc(Pair::new(vals[0].get(), vals[1].get()))),
            BuiltinFunc::List => ctx.alloc_list(vals.iter().map(Cell::get)),
        }
    }
}

#[derive(Clone, Eq)]
// An expression is atomic if:
// * it is guaranteed to terminate;
// * it causes no side effects;
// * it causes no control effects; and
// * it never produces an error.
pub(crate) enum AtomicExpression<'gc> {
    Value(Value<'gc>),
    Variable(VariableId),
}

impl PartialEq for AtomicExpression<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (AtomicExpression::Value(val1), AtomicExpression::Value(val2)) => val1.deep_eq(val2),
            (AtomicExpression::Variable(var1), AtomicExpression::Variable(var2)) => var1.eq(var2),
            (..) => false,
        }
    }
}

impl Debug for AtomicExpression<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            AtomicExpression::Value(val) => write!(fmt, "{:?}", val),
            AtomicExpression::Variable(var) => write!(fmt, "{:?}", var),
        }
    }
}

// pub enum TestExpression {
//     IsFalse(Value),
//     IsLt(AtomicExpression, AtomicExpression),
//     IsLtEq(AtomicExpression, AtomicExpression),
// }

// All values must be immediate expressions.
// NOTE: In A-Normal Form, all non-atomic (complex) expressions must:
// * be let-bound; OR
// * appear in tail position.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) enum ComplexExpression<'gc> {
    Atomic(AtomicExpression<'gc>),

    If {
        test: AtomicExpression<'gc>,
        consequent: Box<Expression<'gc>>,
        alternate: Box<Expression<'gc>>,
    },

    UnaryOp {
        operator: UnaryOp,
        argument: VariableId,
    },

    BinaryOp {
        operator: BinaryOp,
        arguments: (AtomicExpression<'gc>, AtomicExpression<'gc>),
    },

    Display {
        argument: AtomicExpression<'gc>,
    },

    Call {
        function: VariableId,
        arguments: Box<[AtomicExpression<'gc>]>,
    },

    Recurse {
        arguments: Box<[AtomicExpression<'gc>]>,
    },

    CallBuiltin {
        function: BuiltinFunc,
        arguments: Box<[AtomicExpression<'gc>]>,
    },

    Function {
        name: Option<Atom>,
        parameters: Box<[VariableId]>,
        upvalues: Box<[VariableId]>,
        body: Box<Expression<'gc>>,
    },
    // Loop {
    //     id: VariableId,
    //     parameters: Box<[(VariableId, AtomicExpression<'gc>)]>,
    //     bind: Box<[Binding<'gc>]>,
    //     next: Box<[AtomicExpression<'gc>]>,
    // },

    // Break {
    //     id: VariableId,
    //     body: Box<Expression<'gc>>,
    // },
}

// In ANF form. Either a LET binding or a compound expression.
// https://www.cs.swarthmore.edu/~jpolitz/cs75/s16/n_anf-tutorial.html
// https://course.ccs.neu.edu/cs4410/lec_anf_notes.html
// http://matt.might.net/articles/a-normalization/

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) enum BindingKind {
    Local,
    // Mutable,
    Temporary,
}

#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Binding<'gc> {
    pub(crate) variable: VariableId,
    pub(crate) kind: BindingKind,
    pub(crate) init: ComplexExpression<'gc>,
}

impl Debug for Binding<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(
            fmt,
            "{:?} {:?} := {:#?}",
            self.kind, self.variable, self.init
        )
    }
}

// All values must be immediate expressions.
// NOTE: In A-Normal Form, all non-atomic (complex) expressions must:
// * be let-bound; OR
// * appear in tail position.
#[derive(Clone, PartialEq, Eq)]
pub struct Expression<'gc> {
    pub(crate) bind: Box<[Binding<'gc>]>,
    pub(crate) tail: ComplexExpression<'gc>,
}

impl Debug for Expression<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        let mut bind = self.bind.iter();

        if let Some(first) = bind.next() {
            writeln!(fmt)?;
            writeln!(fmt, "let {:?}", first)?;
            for next in bind {
                writeln!(fmt, "    {:?}", next)?;
            }
        }

        write!(fmt, "{:?}", self.tail)
    }
}

#[derive(Default, Debug)]
pub(super) struct ExpressionBuilder<'gc> {
    bind: Vec<Binding<'gc>>,
    tail: ComplexExpression<'gc>,
}

pub(super) trait GenVariable {
    fn gen_variable(&mut self) -> VariableId;
}

impl<'gc> ExpressionBuilder<'gc> {
    pub(crate) fn take(&mut self) -> Expression<'gc> {
        take(self).into()
    }

    pub(crate) fn insert_expression(
        &mut self,
        context: &mut impl GenVariable,
        expr: Expression<'gc>,
    ) -> AtomicExpression<'gc> {
        self.bind.append(&mut expr.bind.into_vec());

        if let ComplexExpression::Atomic(atomic) = expr.tail {
            atomic
        } else {
            let variable = context.gen_variable();
            self.bind.push(Binding {
                variable,
                init: expr.tail,
                kind: BindingKind::Temporary,
            });

            variable.into()
        }
    }

    pub(crate) fn insert_expressions(
        &mut self,
        context: &mut impl GenVariable,
        exprs: impl Iterator<Item = Expression<'gc>>,
    ) -> Box<[AtomicExpression<'gc>]> {
        exprs
            .map(|expr| self.insert_expression(context, expr))
            .collect()
    }

    pub(crate) fn prepend_binding(
        &mut self,
        variable: VariableId,
        expr: Expression<'gc>,
        kind: BindingKind,
    ) {
        let mut bind = vec![Binding {
            variable,
            init: expr.tail,
            kind,
        }];

        bind.append(&mut expr.bind.into_vec());
        bind.append(&mut self.bind);
        self.bind = bind;
    }

    pub(crate) fn append_binding(
        &mut self,
        variable: VariableId,
        expr: Expression<'gc>,
        kind: BindingKind,
    ) {
        self.bind.append(&mut expr.bind.into_vec());
        self.bind.push(Binding {
            variable,
            init: expr.tail,
            kind,
        });
    }

    pub(crate) fn append_expression(&mut self, expr: Expression<'gc>) -> &mut Self {
        debug_assert_eq!(self.tail, Value::NIL.into());
        self.bind.append(&mut expr.bind.into_vec());
        self.tail = expr.tail;
        self
    }

    pub(crate) fn assign_tail(&mut self, tail: ComplexExpression<'gc>) {
        debug_assert_eq!(self.tail, Value::NIL.into());
        self.tail = tail;
    }
}

impl<'gc> From<Expression<'gc>> for ExpressionBuilder<'gc> {
    fn from(Expression { bind, tail }: Expression<'gc>) -> Self {
        Self {
            bind: bind.into_vec(),
            tail,
        }
    }
}

impl<'gc> From<ExpressionBuilder<'gc>> for Expression<'gc> {
    fn from(ExpressionBuilder { bind, tail }: ExpressionBuilder<'gc>) -> Self {
        Self {
            bind: bind.into_boxed_slice(),
            tail,
        }
    }
}

impl<'gc> Expression<'gc> {
    pub(crate) fn as_value(&self) -> Option<&Value<'gc>> {
        if let ComplexExpression::Atomic(AtomicExpression::Value(value)) = &self.tail {
            Some(value)
        } else {
            None
        }
    }
}

impl Default for Expression<'static> {
    fn default() -> Self {
        Value::NIL.into()
    }
}

impl Default for ComplexExpression<'static> {
    fn default() -> Self {
        Value::NIL.into()
    }
}

impl Default for AtomicExpression<'static> {
    fn default() -> Self {
        Value::NIL.into()
    }
}

impl<'gc> From<ComplexExpression<'gc>> for Expression<'gc> {
    fn from(tail: ComplexExpression<'gc>) -> Self {
        Self {
            bind: Box::new([]),
            tail,
        }
    }
}

impl<'gc> From<AtomicExpression<'gc>> for Expression<'gc> {
    fn from(atomic: AtomicExpression<'gc>) -> Self {
        ComplexExpression::from(atomic).into()
    }
}

impl<'gc> From<Value<'gc>> for Expression<'gc> {
    fn from(value: Value<'gc>) -> Self {
        ComplexExpression::from(value).into()
    }
}

impl<'gc> From<VariableId> for Expression<'gc> {
    fn from(variable: VariableId) -> Self {
        ComplexExpression::from(variable).into()
    }
}

impl<'gc> From<AtomicExpression<'gc>> for ComplexExpression<'gc> {
    fn from(atomic: AtomicExpression<'gc>) -> Self {
        Self::Atomic(atomic)
    }
}

impl<'gc> From<Value<'gc>> for ComplexExpression<'gc> {
    fn from(value: Value<'gc>) -> Self {
        Self::Atomic(value.into())
    }
}

impl<'gc> From<VariableId> for ComplexExpression<'gc> {
    fn from(variable: VariableId) -> Self {
        Self::Atomic(variable.into())
    }
}

impl<'gc> From<Value<'gc>> for AtomicExpression<'gc> {
    fn from(value: Value<'gc>) -> Self {
        Self::Value(value)
    }
}

impl<'gc> From<VariableId> for AtomicExpression<'gc> {
    fn from(variable: VariableId) -> Self {
        Self::Variable(variable)
    }
}

impl Display for UnaryOp {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            UnaryOp::Car => write!(fmt, "car"),
            UnaryOp::Cdr => write!(fmt, "cdr"),
            UnaryOp::IsNil => write!(fmt, "is-nil"),
            UnaryOp::IsBool => write!(fmt, "is-bool"),
            UnaryOp::IsChar => write!(fmt, "is-char"),
            UnaryOp::IsSymbol => write!(fmt, "is-symbol"),
            UnaryOp::IsNumber => write!(fmt, "is-number"),
            UnaryOp::IsString => write!(fmt, "is-string"),
            UnaryOp::IsPair => write!(fmt, "is-pair"),
            UnaryOp::IsVector => write!(fmt, "is-vector"),
            UnaryOp::IsClosure => write!(fmt, "is-closure"),
            UnaryOp::IsFunction => write!(fmt, "is-function"),
        }
    }
}

impl Display for BinaryOp {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            BinaryOp::IsEq => write!(fmt, "is-eq"),
            BinaryOp::IsGt => write!(fmt, "is-gt"),
            BinaryOp::IsGtEq => write!(fmt, "is-gt-eq"),
            BinaryOp::IsLt => write!(fmt, "is-lt"),
            BinaryOp::IsLtEq => write!(fmt, "is-lt-eq"),
            BinaryOp::Add => write!(fmt, "add"),
            BinaryOp::Mul => write!(fmt, "mul"),
            BinaryOp::Sub => write!(fmt, "sub"),
            BinaryOp::Div => write!(fmt, "div"),
            BinaryOp::Rem => write!(fmt, "rem"),
        }
    }
}

impl Display for BuiltinFunc {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            BuiltinFunc::Cons => write!(fmt, "cons"),
            BuiltinFunc::List => write!(fmt, "list"),
        }
    }
}

static_assert_size!(AtomicExpression, 16);
// static_assert_size!(ComplexExpression, 48);
// static_assert_size!(Expression, 64);
// static_assert_size!(Binding, 56);
