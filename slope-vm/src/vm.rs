use slope_parse::{parse, ByteRange, ParseError};

use slope_types::{
    Closure, DisplayResolved, Function, Gc, Interner, Managed, Parameters, Root, Trace, Unboxed,
    Value,
};

use std::{
    cell::Cell,
    cmp::max,
    env::current_dir,
    fmt::{self, Debug, Display, Formatter},
    fs::read_to_string,
    io::{self, Write},
    mem::{replace, size_of, swap, take, transmute},
    ops::Range,
    ops::{Deref, DerefMut},
    path::Path,
    pin::Pin,
    ptr, slice,
};

use crate::{
    assemble,
    compile::{self, Compiler, Module, Scope, SyntaxError},
    expr::{BinaryOp, BuiltinFunc, UnaryOp},
    IndexSet,
};

const STACK_SIZE: usize = 1 << 18;

pub struct VirtualMachine {
    context: <EvaluationState<'static> as Root>::Rooted,
}

pub struct MutationContext<'gc> {
    inner: slope_types::MutationContext<'gc, EvaluationState<'gc>>,
}

pub struct AllocationContext<'gc> {
    inner: slope_types::AllocationContext<'gc, EvaluationState<'gc>>,
}

#[derive(Trace)]
pub struct Executable<'gc> {
    code: Pin<Box<[Instruction]>>,
    constants: Pin<Box<[Value<'gc>]>>,
    functions: Pin<Box<[Gc<'gc, Function>]>>,
}

#[derive(Debug)]
pub enum Error {
    Parse(ParseError),
    Syntax(SyntaxError),
    Runtime(RuntimeError),
    Io(io::Error),
}

#[derive(Debug, Clone)]
pub enum RuntimeError {
    ExpectedClosure { found: String },
    // ExpectedList,
    // ExpectedNumeric,
    InvalidArguments { expected: u16, actual: u16 },
    // FloatingPointOverflow,
    StackOverflow,
}

impl Error {
    pub fn origin(&self) -> Option<ByteRange> {
        match self {
            Error::Parse(err) => Some(err.origin()),
            Error::Syntax(err) => Some(err.origin),
            Error::Runtime(_) => None,
            Error::Io(_) => None,
        }
    }

    pub fn hint(&self) -> Option<String> {
        None
        // match &self.reason {
        //     Error::InvalidSyntax { expected } => Some(format!("expected {}", expected)),
        // }
    }
}

pub struct DisplayValue<'gc> {
    value: Value<'gc>,
    context: MutationContext<'gc>,
}

pub struct DisplayExecutable<'gc> {
    context: MutationContext<'gc>,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Trace)]
pub struct ConstantIndex(u16);

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Trace)]
pub struct UpvalueIndex(u16);

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Trace)]
pub struct FunctionIndex(u16);

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Trace)]
pub struct BuiltinIndex(u16);

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Trace)]
pub struct RegisterIndex(u16);

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Trace)]
pub struct RegisterRange {
    start: RegisterIndex,
    len: u16,
}

#[derive(Root)]
pub struct EvaluationState<'gc> {
    interner: Interner,
    loader: Loader,
    scope: Scope<'gc>,
    stack: Pin<Box<[Cell<Value<'gc>>]>>,
    frame: Frame<'gc>,
    frames: Vec<Frame<'gc>>,
    executable: Executable<'gc>,
    result: Value<'gc>,
}

#[derive(Default)]
pub struct Loader {}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Trace)]
#[repr(u8)]
pub enum Instruction {
    Jump {
        pos: i32,
    },

    JumpUnless {
        src: RegisterIndex,
        pos: i32,
    },

    // Swap {
    //     src1: RegisterIndex,
    //     src2: RegisterIndex,
    // },
    Copy {
        dst: RegisterIndex,
        src: RegisterIndex,
    },

    CopyConst {
        dst: RegisterIndex,
        idx: ConstantIndex,
    },

    CopyUpval {
        dst: RegisterIndex,
        idx: UpvalueIndex,
    },

    MakeClosure {
        dst: RegisterIndex,
        idx: FunctionIndex,
    },

    Call {
        dst: RegisterIndex,
        arg: u16,
    },

    TailCall {
        dst: RegisterIndex, // TODO: remove this arg?
        arg: u16,
    },

    // CallNative {
    //     src: RegisterRange,
    // },
    Recurse {
        dst: RegisterIndex,
    },

    Leave {
        res: RegisterIndex, // TODO: remove this arg?
    },

    // JumpUnless {
    //     op: BinaryOp,
    //     src1: StackIdx,
    //     src2: StackIdx,
    //     pos: u16,
    // },

    // JumpUnlessC1 {
    //     op: BinaryOp,
    //     src1: ConstantIndex,
    //     src2: StackIdx,
    //     pos: u16,
    // },

    // JumpUnlessC2 {
    //     op: BinaryOp,
    //     src1: StackIdx,
    //     src2: ConstantIndex,
    //     pos: u16,
    // },
    CallBuiltin {
        fun: BuiltinFunc,
        dst: RegisterIndex,
        arg: u16,
    },

    Unary {
        op: UnaryOp,
        dst: RegisterIndex,
        src: RegisterIndex,
    },

    Binary {
        op: BinaryOp,
        dst: RegisterIndex,
        src1: RegisterIndex,
        src2: RegisterIndex,
    },

    BinaryConst1 {
        op: BinaryOp,
        dst: RegisterIndex,
        src1: ConstantIndex,
        src2: RegisterIndex,
    },

    BinaryConst2 {
        op: BinaryOp,
        dst: RegisterIndex,
        src1: RegisterIndex,
        src2: ConstantIndex,
    },

    Display {
        src: RegisterIndex,
    },
}

static_assert_size!(Instruction, 8);

#[derive(Trace)]
struct Frame<'gc> {
    closure: Gc<'gc, Closure<'gc>>,
    code_ptr: *const Instruction,
    stack_ptr: *const Cell<Value<'gc>>,
}

impl VirtualMachine {
    pub fn with_parameters(parameters: Parameters) -> Self {
        Self {
            context: EvaluationState::root(parameters),
        }
    }

    pub fn result(&mut self) -> DisplayValue<'_> {
        let context = self.mutate();
        DisplayValue {
            value: context.result,
            context,
        }
    }

    pub fn load_prelude(&mut self, source: &str) -> Result<(), Error> {
        let mut ctx = self.mutate_alloc();

        let node = parse(&source).collect::<Result<Vec<_>, _>>()?;

        let dir = current_dir()?;
        let mut compiler = Compiler::new(&mut ctx, &dir);
        let expr = compiler.compile(&node)?;
        ctx.scope = take(compiler.scope());

        debug_assert!(expr == Value::NIL.into());
        Ok(())
    }

    pub fn evaluate(&mut self, source: &str) -> Result<(), Error> {
        let mut ctx = self.mutate_alloc();

        let node = parse(&source).collect::<Result<Vec<_>, _>>()?;

        let dir = current_dir()?;
        // fixme: compiler implicitly takes scope out of ctx
        let mut compiler = Compiler::new(&mut ctx, &dir);
        let expr = compiler.compile(&node);
        ctx.scope = take(compiler.scope());

        let exec = assemble::assemble(&mut ctx, expr?);

        let func = exec
            .functions
            .last()
            .copied()
            .expect("no functions in executable");

        ctx.frame = Frame {
            closure: ctx.alloc(Closure::from(func)),
            code_ptr: unsafe { exec.code.as_ptr().add(func.offset) },
            stack_ptr: ctx.stack.as_ptr(),
        };

        ctx.executable = exec;

        drop(ctx);

        unsafe {
            self.execute()?;
        }

        Ok(())
    }

    pub fn mutate(&mut self) -> MutationContext<'_> {
        MutationContext {
            inner: self.context.mutate(),
        }
    }

    pub fn mutate_alloc(&mut self) -> AllocationContext<'_> {
        AllocationContext {
            inner: self.context.mutate_alloc(),
        }
    }

    pub fn disasm(&mut self) -> DisplayExecutable<'_> {
        DisplayExecutable {
            context: self.mutate(),
        }
    }

    // This function requires:
    // * the instructions in the executable to be valid
    // * the current frame to be valid
    // * no other call frames to be in the vector of frames
    unsafe fn execute(&mut self) -> Result<(), RuntimeError> {
        log::trace!("executing code:\n{}", self.disasm());

        let stdout = io::stdout();
        let mut stdout = stdout.lock();

        loop {
            let mut ctx = self.mutate();

            let ins = ctx.next_instruction();
            log::trace!("executing: {}", ins);

            match ins {
                Instruction::Jump { pos } => {
                    ctx.jump(pos);
                }

                Instruction::JumpUnless { src, pos } => {
                    if ctx.stack_get(src).is_false() {
                        ctx.jump(pos);
                    }
                }

                // Instruction::Swap { src1, src2 } => {
                //     ctx.stack_swap(src1, src2);
                // }
                Instruction::Copy { dst, src } => {
                    let val = ctx.stack_get(src);
                    ctx.stack_set(dst, val);
                }

                Instruction::CopyConst { dst, idx } => {
                    let val = ctx.const_get(idx);
                    ctx.stack_set(dst, val);
                }

                Instruction::CopyUpval { dst, idx } => {
                    let val = ctx.upval_get(idx);
                    ctx.stack_set(dst, val);
                }

                Instruction::MakeClosure { dst, idx } => {
                    let mut ctx = self.mutate_alloc();
                    let function = ctx.function_get(idx);
                    let closure = ctx.alloc(Closure::from(function));
                    ctx.stack_set(dst, closure.into());
                    ctx.assign_upvalues(closure);
                }

                Instruction::Call { dst, arg } => {
                    let closure = ctx.stack_get_closure(dst, arg)?;
                    ctx.push_frame(dst, closure)?;
                }

                Instruction::TailCall { dst, arg } => {
                    let closure = ctx.stack_get_closure(dst, arg)?;
                    ctx.frame = ctx.create_frame(dst, closure)?;
                }

                Instruction::Recurse { dst } => {
                    let closure = ctx.frame.closure;
                    ctx.push_frame(dst, closure)?;
                }

                Instruction::Leave { res } => {
                    let res = ctx.stack_get(res);
                    if let Some(popped) = ctx.frames.pop() {
                        ctx.stack_set(RegisterIndex(0), res);
                        drop(replace(&mut ctx.frame, popped));
                    } else {
                        // TODO this is a bit of a wart; we want to return a value.
                        ctx.result = res;
                        return Ok(());
                    }
                }

                Instruction::CallBuiltin { fun, dst, arg } => {
                    let mut ctx = self.mutate_alloc();
                    let src = ctx.stack_slice(dst, arg);
                    let val = fun.apply(&mut ctx, src);
                    ctx.stack_set(dst, val);
                }

                Instruction::Unary { op, dst, src } => {
                    let src = ctx.stack_get(src);
                    let val = op.apply(src);
                    ctx.stack_set(dst, val);
                }

                Instruction::Binary {
                    op,
                    dst,
                    src1,
                    src2,
                } => {
                    let src1 = ctx.stack_get(src1);
                    let src2 = ctx.stack_get(src2);
                    let val = op.apply(src1, src2);
                    ctx.stack_set(dst, val);
                }

                Instruction::BinaryConst1 {
                    op,
                    dst,
                    src1,
                    src2,
                } => {
                    let src1 = ctx.const_get(src1);
                    let src2 = ctx.stack_get(src2);
                    let val = op.apply(src1, src2);
                    ctx.stack_set(dst, val);
                }

                Instruction::BinaryConst2 {
                    op,
                    dst,
                    src1,
                    src2,
                } => {
                    let src1 = ctx.stack_get(src1);
                    let src2 = ctx.const_get(src2);
                    let val = op.apply(src1, src2);
                    ctx.stack_set(dst, val);
                }

                Instruction::Display { src } => {
                    write!(
                        stdout,
                        "{}",
                        DisplayValue {
                            value: ctx.stack_get(src),
                            context: ctx,
                        }
                    )
                    .expect("write failed");
                }
            }

            log::trace!("stack: {:?}", self.mutate().stack_slots());
        }
    }
}

impl Default for VirtualMachine {
    fn default() -> Self {
        Self::with_parameters(Parameters::default())
    }
}

impl<'gc> Deref for MutationContext<'gc> {
    type Target = EvaluationState<'gc>;

    fn deref(&self) -> &Self::Target {
        &self.inner.root
    }
}

impl<'gc> DerefMut for MutationContext<'gc> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner.root
    }
}

impl<'gc> AllocationContext<'gc> {
    pub fn alloc<T>(&mut self, data: T) -> Gc<'gc, T>
    where
        T: Managed,
    {
        self.inner.alloc(data)
    }

    pub fn alloc_list<I>(&mut self, values: I) -> Value<'gc>
    where
        I: ExactSizeIterator<Item = Value<'gc>> + DoubleEndedIterator<Item = Value<'gc>>,
    {
        self.inner.alloc_list(values)
    }

    pub(crate) fn scope(&mut self) -> &mut Scope<'gc> {
        &mut self.scope
    }
}

impl<'gc> Deref for AllocationContext<'gc> {
    type Target = EvaluationState<'gc>;

    fn deref(&self) -> &Self::Target {
        &self.inner.root
    }
}

impl<'gc> DerefMut for AllocationContext<'gc> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner.root
    }
}

impl<'gc> EvaluationState<'gc> {
    pub(crate) fn interner(&mut self) -> &mut Interner {
        &mut self.interner
    }

    pub(crate) fn loader(&mut self) -> &mut Loader {
        &mut self.loader
    }

    #[inline(always)]
    fn push_frame(
        &mut self,
        dst: RegisterIndex,
        closure: Gc<'gc, Closure<'gc>>,
    ) -> Result<(), RuntimeError> {
        let frame = self.create_frame(dst, closure)?;
        self.frames.push(replace(&mut self.frame, frame));
        Ok(())
    }

    #[inline(always)]
    fn create_frame(
        &mut self,
        dst: RegisterIndex,
        closure: Gc<'gc, Closure<'gc>>,
    ) -> Result<Frame<'gc>, RuntimeError> {
        debug_assert!(self.registers() > dst.0);
        let code_ptr = unsafe { self.executable.code.as_ptr().add(closure.function.offset) };
        let stack_ptr = unsafe { self.frame.stack_ptr.add(dst.0 as usize) };

        if unsafe {
            stack_ptr.add(closure.function.registers as usize)
                > self.stack.as_ptr().add(self.stack.len())
        } {
            return Err(RuntimeError::StackOverflow);
        }

        Ok(Frame {
            closure,
            code_ptr,
            stack_ptr,
        })
    }

    fn registers(&self) -> u16 {
        self.frame.closure.function.registers
    }

    fn stack_offset(&self) -> usize {
        let offset = self.frame.stack_ptr as usize - self.stack.as_ptr() as usize;
        debug_assert!(offset % size_of::<Value>() == 0);
        offset / size_of::<Value>()
    }

    fn code_len(&self) -> usize {
        self.executable.code.len()
    }

    fn code_offset(&self) -> usize {
        let offset = self.frame.code_ptr as usize - self.executable.code.as_ptr() as usize;
        debug_assert!(offset % size_of::<Instruction>() == 0);
        offset / size_of::<Instruction>()
    }

    fn stack_slots(&self) -> &[Value<'gc>] {
        let len = self.stack_offset() + self.registers() as usize;
        if cfg!(debug_assertions) {
            unsafe { transmute(&self.stack[0..len]) }
        } else {
            unsafe { transmute(self.stack.get_unchecked(0..len)) }
        }
    }

    // fn stack_swap(&self, reg_a: RegisterIndex, reg_b: RegisterIndex) {
    //     debug_assert!(self.registers() > reg_a.0);
    //     debug_assert!(self.registers() > reg_b.0);
    //     unsafe {
    //         Cell::swap(
    //             &*self.frame.stack_ptr.add(reg_a.0 as usize),
    //             &*self.frame.stack_ptr.add(reg_b.0 as usize),
    //         );
    //     }
    // }

    fn stack_slice(&self, src: RegisterIndex, len: u16) -> &'gc [Cell<Value<'gc>>] {
        debug_assert!(self.registers() >= src.0 + len);
        unsafe { slice::from_raw_parts(self.frame.stack_ptr.add(src.0 as usize), len as usize) }
    }

    fn stack_get(&self, reg: RegisterIndex) -> Value<'gc> {
        debug_assert!(self.registers() > reg.0);
        unsafe { &*self.frame.stack_ptr.add(reg.0 as usize) }.get()
    }

    fn stack_set(&self, reg: RegisterIndex, value: Value<'gc>) {
        debug_assert!(self.registers() > reg.0);
        unsafe { &*self.frame.stack_ptr.add(reg.0 as usize) }.set(value)
    }

    fn stack_get_closure(
        &self,
        dst: RegisterIndex,
        arg: u16,
    ) -> Result<Gc<'gc, Closure<'gc>>, RuntimeError> {
        match self.stack_get(dst).unbox() {
            Unboxed::Closure(closure) => {
                if arg != closure.function.parameters {
                    Err(RuntimeError::InvalidArguments {
                        expected: closure.function.parameters,
                        actual: arg,
                    })
                } else {
                    Ok(closure)
                }
            }

            unboxed => Err(RuntimeError::ExpectedClosure {
                found: unboxed.to_string(),
            }),
        }
    }

    fn const_get(&self, idx: ConstantIndex) -> Value<'gc> {
        if cfg!(debug_assertions) {
            self.executable.constants[idx.0 as usize]
        } else {
            unsafe { *self.executable.constants.get_unchecked(idx.0 as usize) }
        }
    }

    fn upval_get(&self, idx: UpvalueIndex) -> Value<'gc> {
        if cfg!(debug_assertions) {
            self.frame.closure.upvalues()[idx.0 as usize].get()
        } else {
            unsafe { &*self.frame.closure.upvalues().get_unchecked(idx.0 as usize) }.get()
        }
    }

    fn function_get(&self, idx: FunctionIndex) -> Gc<'gc, Function> {
        if cfg!(debug_assertions) {
            self.executable.functions[idx.0 as usize]
        } else {
            unsafe { *self.executable.functions.get_unchecked(idx.0 as usize) }
        }
    }

    fn assign_upvalues(&self, closure: Gc<'gc, Closure<'gc>>) {
        for (upval, &reg) in closure
            .upvalues()
            .iter()
            .zip(closure.function.upvalues.iter())
        {
            upval.set(self.stack_get(RegisterIndex(reg)))
        }
    }

    fn jump(&mut self, offset: i32) {
        self.frame.code_ptr = unsafe { self.frame.code_ptr.offset(offset as isize) };

        // Can be directly past the final instruction, iff not dereferenced.
        debug_assert!(self.code_len() >= self.code_offset());
    }

    fn next_instruction(&mut self) -> Instruction {
        debug_assert!(self.code_len() > self.code_offset());
        let ins = unsafe { *self.frame.code_ptr };
        self.jump(1);
        ins
    }
}

impl<'gc> Default for EvaluationState<'gc> {
    fn default() -> Self {
        Self {
            interner: Default::default(),
            loader: Default::default(),
            scope: Default::default(),
            stack: unsafe { transmute(vec![Value::ZERO; STACK_SIZE].into_boxed_slice()) },
            frame: Frame::<'gc> {
                closure: unsafe { Gc::dangling() },
                code_ptr: ptr::null(),
                stack_ptr: ptr::null(),
            },
            frames: vec![],
            executable: Executable {
                code: Box::pin([]),
                constants: Box::pin([]),
                functions: Box::pin([]),
            },
            result: Value::NIL,
        }
    }
}

unsafe impl<'gc> Trace for EvaluationState<'gc> {
    fn trace(&self, tracer: &mut impl slope_types::Tracer) {
        for slot in self.stack_slots() {
            slot.trace(tracer);
        }

        for frame in self.frames.iter() {
            frame.closure.trace(tracer);
        }

        self.frame.closure.trace(tracer);
        self.executable.trace(tracer);
    }
}

impl Loader {
    pub fn read(&self, path: &Path) -> Result<String, Error> {
        Ok(read_to_string(path)?)
    }
}

impl<'gc> Executable<'gc> {
    pub fn disasm(&self) -> impl Iterator<Item = &Instruction> {
        self.code.iter()
    }
}

impl Display for DisplayValue<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        self.value.fmt_resolved(fmt, &self.context.interner)
    }
}

impl Display for DisplayExecutable<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        self.context
            .executable
            .fmt_resolved(fmt, &self.context.interner)
    }
}

impl Display for RuntimeError {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            RuntimeError::ExpectedClosure { .. } => write!(fmt, "expected closure"),
            RuntimeError::InvalidArguments { .. } => write!(fmt, "invalid arguments"),
            RuntimeError::StackOverflow => write!(fmt, "stack overflow"),
        }
    }
}

impl From<ParseError> for Error {
    fn from(error: ParseError) -> Self {
        Self::Parse(error)
    }
}

impl From<SyntaxError> for Error {
    fn from(error: SyntaxError) -> Self {
        Self::Syntax(error)
    }
}

impl From<RuntimeError> for Error {
    fn from(error: RuntimeError) -> Self {
        Self::Runtime(error)
    }
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

impl Display for Error {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Error::Parse(err) => write!(fmt, "{}", err),
            Error::Syntax(err) => write!(fmt, "{}", err),
            Error::Runtime(err) => write!(fmt, "{}", err),
            Error::Io(err) => write!(fmt, "{}", err),
        }
    }
}

#[derive(Default, Debug)]
pub struct ExecutableAssembler<'gc> {
    code: Vec<Instruction>,
    constants: IndexSet<Value<'gc>>,
    functions: Vec<Gc<'gc, Function>>,
}

#[derive(Default, Debug)]
pub struct ReverseFunctionAssembler {
    code: Vec<Instruction>,
    upvalues: Box<[u16]>,
    parameters: u16,
    registers: u16,
    freed: IndexSet<u16>,
}

// Assemblers are in this module to ensure the indices are not out of bounds.
impl<'gc> ExecutableAssembler<'gc> {
    pub fn add_func(
        &mut self,
        ctx: &mut AllocationContext<'gc>,
        ReverseFunctionAssembler {
            mut code,
            upvalues,
            parameters,
            registers,
            ..
        }: ReverseFunctionAssembler,
    ) -> FunctionIndex {
        let index = self.functions.len();

        if index > u16::MAX as usize {
            panic!("too many functions");
        }

        if upvalues.len() > u16::MAX as usize {
            panic!("too many upvalues");
        }

        if let Instruction::Leave { .. } | Instruction::TailCall { .. } = code[0] {
            // ok
        } else {
            panic!("last instruction must leave function");
        }

        let offset = self.code.len();

        for (index, ins) in code.iter_mut().rev().enumerate() {
            if let Instruction::Jump { pos } = ins {
                if *pos == 0 {
                    *pos = -(index as i32 + 1);
                }
            }
        }

        self.code.extend(code.into_iter().rev());

        self.functions.push(ctx.alloc(Function {
            offset,
            upvalues,
            parameters,
            registers,
        }));

        FunctionIndex(index as u16)
    }

    pub fn add_const(&mut self, value: Value<'gc>) -> ConstantIndex {
        let (index, _) = self.constants.insert_full(value);

        if index > u16::MAX as usize {
            panic!("too many constants");
        }

        ConstantIndex(index as u16)
    }

    pub fn finalize(self) -> Executable<'gc> {
        assert!(!self.functions.is_empty());

        Executable {
            code: self.code.into_boxed_slice().into(),
            constants: self.constants.into_iter().collect::<Box<_>>().into(),
            functions: self.functions.into_boxed_slice().into(),
        }
    }
}

impl ReverseFunctionAssembler {
    pub fn alloc_params(&mut self, parameters: usize) -> impl Iterator<Item = RegisterIndex> + '_ {
        if parameters > u16::MAX as usize {
            panic!("too many parameters");
        }

        self.parameters = self
            .parameters
            .checked_add(parameters as u16)
            .expect("too many parameters");

        (0..parameters).map(move |_| self.alloc_stack())
    }

    pub fn assign_upvalues(
        &mut self,
        upvalues: impl ExactSizeIterator<Item = RegisterIndex>,
    ) -> impl Iterator<Item = UpvalueIndex> + '_ {
        if upvalues.len() > u16::MAX as usize {
            panic!("too many upvalues");
        }

        self.upvalues = upvalues.map(|idx| idx.0).collect();
        (0..self.upvalues.len()).map(|idx| UpvalueIndex(idx as u16))
    }

    pub fn alloc_stack(&mut self) -> RegisterIndex {
        if let Some(&index) = self.freed.iter().next() {
            // if let Some(&index) = self.freed.iter().rev().next() { // TODO FIX THIS
            self.freed.remove(&index);
            RegisterIndex(index)
        } else {
            let index = self.registers;
            self.registers = self.registers.checked_add(1).expect("too many registers");
            RegisterIndex(index)
        }
    }

    pub fn alloc_stack_range(&mut self, len: u16) -> RegisterRange {
        let mut start = self.registers;

        while start > 0 {
            if let Some(&free) = self.freed.get(&(start - 1)) {
                self.freed.remove(&free);
                start = free;
            } else {
                break;
            }
        }

        self.registers = max(
            self.registers,
            start.checked_add(len).expect("too many registers"),
        );

        RegisterRange {
            start: RegisterIndex(start),
            len,
        }
    }

    pub fn free_stack(&mut self, index: RegisterIndex) {
        self.freed.insert(index.0);
    }

    pub fn emit(&mut self, instruction: Instruction) {
        self.code.push(instruction);
    }

    pub fn last(&mut self) -> Option<Instruction> {
        self.code.last().copied()
    }

    pub fn pop(&mut self) {
        self.code.pop();
    }

    pub fn len(&self) -> usize {
        self.code.len()
    }
}

impl RegisterRange {
    pub(crate) fn start(&self) -> RegisterIndex {
        self.start
    }

    pub(crate) fn iter(
        &self,
    ) -> impl DoubleEndedIterator<Item = RegisterIndex> + ExactSizeIterator<Item = RegisterIndex>
    {
        (self.start.0..self.start.0 + self.len).map(RegisterIndex)
    }
}

impl Display for ConstantIndex {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "(const {})", self.0)
    }
}

impl Debug for ConstantIndex {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "{}", self.0)
    }
}

impl Display for UpvalueIndex {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "(upval {})", self.0)
    }
}

impl Debug for UpvalueIndex {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "{}", self.0)
    }
}

impl Display for FunctionIndex {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "(func {})", self.0)
    }
}

impl Debug for FunctionIndex {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "{}", self.0)
    }
}

impl Display for RegisterIndex {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "{}", self.0)
    }
}

impl Debug for RegisterIndex {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "{}", self.0)
    }
}

impl Display for RegisterRange {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "{} {}", self.start, self.len)
    }
}

impl Display for Instruction {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Instruction::Copy { dst, src } => write!(fmt, "(copy {} {})", dst, src),

            // Instruction::Swap { src1, src2 } => write!(fmt, "(swap {} {})", src1, src2),
            Instruction::CopyConst { dst, idx } => write!(fmt, "(copy {} {})", dst, idx),

            Instruction::CopyUpval { dst, idx } => write!(fmt, "(copy {} {})", dst, idx),

            Instruction::MakeClosure { dst, idx } => write!(fmt, "(make-closure {} {})", dst, idx),

            Instruction::Call { dst, arg } => write!(fmt, "(call {} {})", dst, arg),

            Instruction::TailCall { dst, arg } => write!(fmt, "(tail-call {} {})", dst, arg),

            Instruction::Recurse { dst } => write!(fmt, "(recurse {})", dst),

            Instruction::Leave { res } => write!(fmt, "(leave {})", res),

            Instruction::Jump { pos } => write!(fmt, "(jump {})", pos),

            Instruction::JumpUnless { src, pos } => write!(fmt, "(jump-unless {} {})", src, pos),

            Instruction::Unary { op, dst, src } => write!(fmt, "({} {} {})", op, dst, src),

            Instruction::Binary {
                op,
                dst,
                src1,
                src2,
            } => write!(fmt, "({} {} {} {})", op, dst, src1, src2),

            Instruction::BinaryConst1 {
                op,
                dst,
                src1,
                src2,
            } => write!(fmt, "({} {} {} {})", op, dst, src1, src2),

            Instruction::BinaryConst2 {
                op,
                dst,
                src1,
                src2,
            } => write!(fmt, "({} {} {} {})", op, dst, src1, src2),

            Instruction::CallBuiltin { fun, dst, arg } => write!(fmt, "({} {} {})", fun, dst, arg),

            Instruction::Display { src } => write!(fmt, "(display {})", src),
        }
    }
}

impl DisplayResolved for Executable<'_> {
    fn fmt_resolved(&self, fmt: &mut Formatter<'_>, interner: &Interner) -> fmt::Result {
        let mut funcs = self.functions.iter().enumerate().peekable();
        while let Some((index, func)) = funcs.next() {
            write!(
                fmt,
                "(func {:<24} ; regs: {}, params: {}, upvals: {}",
                index,
                func.registers,
                func.parameters,
                func.upvalues.len()
            )?;

            let end = funcs
                .peek()
                .map(|f| f.1.offset)
                .unwrap_or_else(|| self.code.len());
            let code = &self.code[func.offset..end];

            for &ins in code {
                match ins {
                    Instruction::CopyConst { idx, .. }
                    | Instruction::BinaryConst1 { src1: idx, .. }
                    | Instruction::BinaryConst2 { src2: idx, .. } => {
                        write!(fmt, "\n  {:<28} ; const: ", ins.to_string())?;
                        self.constants[idx.0 as usize].fmt_resolved(fmt, interner)?;
                    }

                    Instruction::MakeClosure { idx, .. } => {
                        let upvalues = &self.functions[idx.0 as usize].upvalues;

                        if upvalues.is_empty() {
                            write!(fmt, "\n  {}", ins)?;
                        } else {
                            write!(fmt, "\n  {:<28} ; upvals: ", ins.to_string())?;

                            for (upval, &index) in upvalues.iter().enumerate() {
                                write!(fmt, "{} = {}", upval, index)?;

                                if upval + 1 < upvalues.len() {
                                    write!(fmt, ", ")?;
                                }
                            }
                        }
                    }

                    _ => {
                        write!(fmt, "\n  {}", ins)?;
                    }
                }
            }
            writeln!(fmt, ")")?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();

        ctx.executable = Executable {
            code: vec![
                Instruction::CopyConst {
                    idx: ConstantIndex(0),
                    dst: RegisterIndex(0),
                },
                Instruction::Leave {
                    res: RegisterIndex(0),
                },
            ]
            .into_boxed_slice()
            .into(),
            constants: Box::pin([Value::from(1.5)]),
            functions: vec![ctx.alloc(Function {
                offset: 0,
                upvalues: Box::new([]),
                parameters: 0,
                registers: 1,
            })]
            .into_boxed_slice()
            .into(),
        };

        ctx.frame = Frame {
            closure: ctx.alloc(Closure::from(ctx.executable.functions[0])),
            code_ptr: ctx.executable.code.as_ptr(),
            stack_ptr: ctx.stack.as_ptr(),
        };

        drop(ctx);

        unsafe {
            vm.execute().unwrap();
        }

        let ctx = vm.mutate();
        assert_eq!(ctx.result, Value::from(1.5));
    }
}
