use super::{
    expr::{AtomicExpression, Binding, BindingKind, ComplexExpression, Expression, VariableId},
    vm::{
        AllocationContext, Executable, ExecutableAssembler, FunctionIndex, Instruction,
        RegisterIndex, ReverseFunctionAssembler, UpvalueIndex,
    },
    HashMap,
};

#[derive(Default, Debug)]
struct Block {
    func: ReverseFunctionAssembler,
    parameters: Vec<RegisterIndex>,
    variables: HashMap<VariableId, RegisterIndex>,
    upvalues: HashMap<VariableId, UpvalueIndex>,
}

pub(crate) fn assemble<'gc>(
    ctx: &mut AllocationContext<'gc>,
    expr: Expression<'gc>,
) -> Executable<'gc> {
    let mut exec = ExecutableAssembler::default();

    emit_fn(
        ctx,
        &mut exec,
        Default::default(),
        expr,
        &[],
        Default::default(),
    );

    exec.finalize()
}

fn emit_fn<'gc>(
    ctx: &mut AllocationContext<'gc>,
    asm: &mut ExecutableAssembler<'gc>,
    func: ReverseFunctionAssembler,
    expr: Expression<'gc>,
    parameters: &[VariableId],
    upvalues: HashMap<VariableId, UpvalueIndex>,
) -> FunctionIndex {
    let mut block = Block {
        func,
        parameters: Default::default(),
        variables: Default::default(),
        upvalues,
    };

    let res = block.func.alloc_stack();
    block.func.emit(Instruction::Leave { res });

    for (dst, &param) in block.func.alloc_params(parameters.len()).zip(parameters) {
        block.variables.insert(param, dst);
        block.parameters.push(dst);
    }

    block.func.free_stack(res);
    emit_expr(ctx, asm, &mut block, expr, res, Position::Tail);

    for parameter in parameters {
        block.variables.remove(parameter);
    }

    assert!(
        block.variables.is_empty(),
        "variables not initialized: {:?}", block.variables.keys()
    );

    asm.add_func(ctx, block.func)
}

fn emit_expr<'gc>(
    ctx: &mut AllocationContext<'gc>,
    asm: &mut ExecutableAssembler<'gc>,
    block: &mut Block,
    expr: Expression<'gc>,
    dst: RegisterIndex,
    position: Position,
) {
    emit_complex(ctx, asm, block, expr.tail, dst, position);

    for Binding {
        variable,
        init,
        kind,
    } in expr.bind.into_vec().into_iter().rev()
    {
        let dst = variable_pos(block, variable);

        if kind != BindingKind::Local {
            block.func.free_stack(dst);
        }

        emit_complex(ctx, asm, block, init, dst, Position::Body);

        block.func.free_stack(dst);
        block.variables.remove(&variable);
    }
}

fn emit_atomic<'gc>(
    asm: &mut ExecutableAssembler<'gc>,
    block: &mut Block,
    atomic: AtomicExpression<'gc>,
    dst: RegisterIndex,
) {
    match atomic {
        AtomicExpression::Value(value) => {
            let idx = asm.add_const(value);
            block.func.emit(Instruction::CopyConst { dst, idx });
            block.func.free_stack(dst);
        }

        AtomicExpression::Variable(variable) => {
            if let Some(&idx) = block.upvalues.get(&variable) {
                block.func.emit(Instruction::CopyUpval { dst, idx });
                block.func.free_stack(dst);
            } else if let Some(&src) = block.variables.get(&variable) {
                if src != dst {
                    block.copy(dst, src);
                    block.func.free_stack(dst);
                }
            } else {
                block.variables.insert(variable, dst);
            }
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
enum Position {
    Tail,
    Body,
}

fn emit_complex<'gc>(
    ctx: &mut AllocationContext<'gc>,
    asm: &mut ExecutableAssembler<'gc>,
    block: &mut Block,
    complex: ComplexExpression<'gc>,
    dst: RegisterIndex,
    position: Position,
) {
    match complex {
        ComplexExpression::Atomic(atomic) => {
            emit_atomic(asm, block, atomic, dst);
        }

        ComplexExpression::If {
            test,
            consequent,
            alternate,
        } => {
            let final_pos = block.func.len();

            emit_expr(ctx, asm, block, *alternate, dst, position);
            let alt_pos = block.func.len();

            if position == Position::Tail {
                block.func.emit(Instruction::Leave { res: dst });
            } else {
                block.func.emit(Instruction::Jump {
                    pos: (alt_pos - final_pos) as i32,
                });
            }

            emit_expr(ctx, asm, block, *consequent, dst, position);
            let cons_pos = block.func.len();

            if let AtomicExpression::Variable(test) = test {
                block.with_variable(test, |block, src| {
                    block.func.emit(Instruction::JumpUnless {
                        src,
                        pos: (cons_pos - alt_pos) as i32,
                    });
                })
            } else {
                panic!("expected variable");
            }
        }

        ComplexExpression::UnaryOp { operator, argument } => {
            block.with_variable(argument, |block, src| {
                block.func.emit(Instruction::Unary {
                    op: operator,
                    dst,
                    src,
                });
            })
        }

        ComplexExpression::BinaryOp {
            operator,
            arguments: (arg1, arg2),
        } => match (arg1, arg2) {
            (AtomicExpression::Value(_), AtomicExpression::Value(_)) => {
                panic!("expected at least one variable");
            }

            (AtomicExpression::Value(val1), AtomicExpression::Variable(var2)) => {
                let src1 = asm.add_const(val1);
                block.with_variable(var2, |block, src2| {
                    block.func.emit(Instruction::BinaryConst1 {
                        op: operator,
                        dst,
                        src1,
                        src2,
                    });
                });
            }

            (AtomicExpression::Variable(var1), AtomicExpression::Value(val2)) => {
                let src2 = asm.add_const(val2);
                block.with_variable(var1, |block, src1| {
                    block.func.emit(Instruction::BinaryConst2 {
                        op: operator,
                        dst,
                        src1,
                        src2,
                    });
                });
            }

            (AtomicExpression::Variable(var1), AtomicExpression::Variable(var2)) => {
                block.with_variable(var1, |block, src1| {
                    block.with_variable(var2, |block, src2| {
                        block.func.emit(Instruction::Binary {
                            op: operator,
                            dst,
                            src1,
                            src2,
                        });
                    })
                });
            }
        },

        ComplexExpression::Display { .. } => {
            todo!()
            // block.with_variable(test, |block, src| {
            //     block.func.emit(Instruction::JumpUnless {
            //         src,
            //         pos: (cons_pos - alt_pos) as i32,
            //     });
            // })
        }

        ComplexExpression::CallBuiltin {
            function,
            arguments,
        } => {
            let arg = arguments.len() as u16;
            let rng = block.func.alloc_stack_range(arg);
            block.copy(dst, rng.start());

            block.func.emit(Instruction::CallBuiltin {
                fun: function,
                dst: rng.start(),
                arg,
            });

            for (arg, dst) in Vec::from(arguments).into_iter().zip(rng.iter()) {
                emit_atomic(asm, block, arg, dst);
            }
        }

        ComplexExpression::Call {
            function,
            arguments,
        } => {
            let arg = arguments.len() as u16;
            let rng = block.func.alloc_stack_range(arg + 1);
            block.copy(dst, rng.start());

            if position == Position::Tail && rng.start() == dst {
                // TODO Make this work if rng does not start at 0
                block.func.pop();
                block.func.emit(Instruction::TailCall {
                    dst: rng.start(),
                    arg,
                });
            } else {
                block.func.emit(Instruction::Call {
                    dst: rng.start(),
                    arg,
                });
            }

            emit_atomic(asm, block, function.into(), rng.start());

            for (arg, dst) in Vec::from(arguments).into_iter().zip(rng.iter().skip(1)) {
                emit_atomic(asm, block, arg, dst);
            }
        }

        ComplexExpression::Recurse { arguments } => {
            // if position == Position::Tail {
            //     block.func.pop();
            //     block.func.emit(Instruction::Jump { pos: 0 }); // todo clear leave

            //     let params = block.parameters.clone();
            //     for (arg, &dst) in Vec::from(arguments).into_iter().zip(params.iter()) {
            //         let tmp = block.func.alloc_stack();
            //         emit_atomic(asm, block, arg, tmp);
            //         block.copy(dst, tmp);
            //     }
            // } else {
            let arg = arguments.len() as u16;
            let rng = block.func.alloc_stack_range(arg + 1);
            block.copy(dst, rng.start());

            block.func.emit(Instruction::Recurse { dst: rng.start() });

            for (arg, dst) in Vec::from(arguments).into_iter().zip(rng.iter().skip(1)) {
                emit_atomic(asm, block, arg, dst);
            }
            // }
        }

        ComplexExpression::Function {
            parameters,
            upvalues,
            body,
            ..
        } => {
            let mut upvalue_references = HashMap::default();
            let mut load_upvalues = HashMap::<RegisterIndex, UpvalueIndex>::default();

            let mut func = ReverseFunctionAssembler::default();
            let upvalue_idxs = func.assign_upvalues(upvalues.iter().map(|&variable| {
                if let Some(&idx) = block.upvalues.get(&variable) {
                    let dst = block.func.alloc_stack();
                    load_upvalues.insert(dst, idx);
                    dst
                } else {
                    variable_pos(block, variable)
                }
            }));

            for (&variable, upvalue) in upvalues.iter().zip(upvalue_idxs) {
                upvalue_references.insert(variable, upvalue);
            }

            let idx = emit_fn(ctx, asm, func, *body, &parameters, upvalue_references);
            block.func.emit(Instruction::MakeClosure { dst, idx });

            for (dst, idx) in load_upvalues {
                block.func.emit(Instruction::CopyUpval { dst, idx });
            }
        }
    }
}

fn variable_pos(block: &mut Block, variable: VariableId) -> RegisterIndex {
    if let Some(&pos) = block.variables.get(&variable) {
        pos
    } else {
        let pos = block.func.alloc_stack();
        block.variables.insert(variable, pos);
        pos
    }
}

impl Block {
    fn with_variable(&mut self, variable: VariableId, fun: impl FnOnce(&mut Block, RegisterIndex)) {
        if let Some(&idx) = self.upvalues.get(&variable) {
            let dst = self.func.alloc_stack();
            fun(self, dst);
            self.func.emit(Instruction::CopyUpval { dst, idx });
            self.func.free_stack(dst);
        } else {
            let dst = variable_pos(self, variable);
            fun(self, dst);
        }
    }

    fn copy(&mut self, dst: RegisterIndex, src: RegisterIndex) {
        if src == dst {
            return;
        }

        if let Some(Instruction::Leave { res }) = self.func.last() {
            assert!(res == dst);
            self.func.pop();
            self.func.emit(Instruction::Leave { res: src });
        } else {
            self.func.emit(Instruction::Copy { dst, src });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        expr::{BinaryOp, BuiltinFunc, UnaryOp},
        vm::VirtualMachine,
    };
    use slope_types::{Pair, Value};

    #[test]
    fn test_atomic() {
        let _ = simple_logger::init();

        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();
        let pair = Value::from(ctx.alloc(Pair::new(Value::from(1), Value::NIL)));
        let exec = assemble(
            &mut ctx,
            Expression {
                bind: Box::new([]),
                tail: ComplexExpression::Atomic(pair.into()),
            },
        );

        let code = exec.disasm().collect::<Vec<_>>();
        assert!(matches!(code[0], Instruction::CopyConst { .. }));
        assert!(matches!(code[1], Instruction::Leave { .. }));
    }

    #[test]
    fn test_unary_op() {
        let _ = simple_logger::init();

        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();
        let pair = Value::from(ctx.alloc(Pair::new(Value::from(2), Value::NIL)));
        let exec = assemble(
            &mut ctx,
            Expression {
                bind: vec![Binding {
                    variable: VariableId(0),
                    kind: BindingKind::Local,
                    init: pair.into(),
                }]
                .into_boxed_slice(),
                tail: ComplexExpression::UnaryOp {
                    operator: UnaryOp::Car,
                    argument: VariableId(0).into(),
                },
            },
        );

        let code = exec.disasm().collect::<Vec<_>>();
        assert!(matches!(code[0], Instruction::CopyConst { .. }));
        assert!(matches!(
            code[1],
            Instruction::Unary {
                op: UnaryOp::Car,
                ..
            }
        ));
        assert!(matches!(code[2], Instruction::Leave { .. }));
    }

    #[test]
    fn test_binary_op() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();
        let exec = assemble(
            &mut ctx,
            Expression {
                bind: vec![
                    Binding {
                        variable: VariableId(0),
                        kind: BindingKind::Local,
                        init: Value::from(1.5).into(),
                    },
                    Binding {
                        variable: VariableId(1),
                        kind: BindingKind::Local,
                        init: Value::from(2.5).into(),
                    },
                ]
                .into_boxed_slice(),
                tail: ComplexExpression::BinaryOp {
                    operator: BinaryOp::Add,
                    arguments: (VariableId(0).into(), VariableId(1).into()),
                },
            },
        );

        let code = exec.disasm().collect::<Vec<_>>();
        assert!(matches!(code[0], Instruction::CopyConst { .. }));
        assert!(matches!(code[1], Instruction::CopyConst { .. }));
        assert!(matches!(
            code[2],
            Instruction::Binary {
                op: BinaryOp::Add,
                ..
            }
        ));
        assert!(matches!(code[3], Instruction::Leave { .. }));
    }

    #[test]
    fn test_variadic_op() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();
        let exec = assemble(
            &mut ctx,
            Expression {
                bind: vec![
                    Binding {
                        variable: VariableId(0),
                        kind: BindingKind::Local,
                        init: Value::from(1.5).into(),
                    },
                    Binding {
                        variable: VariableId(2),
                        kind: BindingKind::Local,
                        init: Value::from(3.5).into(),
                    },
                    Binding {
                        variable: VariableId(1),
                        kind: BindingKind::Local,
                        init: Value::from(2.5).into(),
                    },
                ]
                .into_boxed_slice(),
                tail: ComplexExpression::CallBuiltin {
                    function: BuiltinFunc::List,
                    arguments: Box::new([
                        VariableId(0).into(),
                        VariableId(1).into(),
                        VariableId(2).into(),
                    ]),
                },
            },
        );

        let code = exec.disasm().collect::<Vec<_>>();
        assert!(matches!(code[0], Instruction::CopyConst { .. }));
        assert!(matches!(code[1], Instruction::CopyConst { .. }));
        assert!(matches!(code[2], Instruction::CopyConst { .. }));
        assert!(matches!(
            code[3],
            Instruction::CallBuiltin {
                fun: BuiltinFunc::List,
                ..
            }
        ));
        assert!(matches!(code[4], Instruction::Leave { .. }));
    }

    #[test]
    fn test_if_true() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();
        let exec = assemble(
            &mut ctx,
            Expression {
                bind: vec![Binding {
                    variable: VariableId(0),
                    kind: BindingKind::Local,
                    init: Value::from(4).into(),
                }]
                .into_boxed_slice(),
                tail: ComplexExpression::If {
                    test: VariableId(0).into(),
                    consequent: Box::new(Value::from(1).into()),
                    alternate: Box::new(Value::from(2).into()),
                },
            },
        );

        let code = exec.disasm().collect::<Vec<_>>();
        assert!(matches!(code[0], Instruction::CopyConst { .. }));
        assert!(matches!(code[1], Instruction::JumpUnless { pos: 2, .. }));
        assert!(matches!(code[2], Instruction::CopyConst { .. }));
        assert!(matches!(code[3], Instruction::Leave { .. }));
        assert!(matches!(code[4], Instruction::CopyConst { .. }));
        assert!(matches!(code[5], Instruction::Leave { .. }));
    }

    #[test]
    fn test_if_false() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();
        let exec = assemble(
            &mut ctx,
            Expression {
                bind: vec![Binding {
                    variable: VariableId(0),
                    kind: BindingKind::Local,
                    init: Value::from(false).into(),
                }]
                .into_boxed_slice(),
                tail: ComplexExpression::If {
                    test: VariableId(0).into(),
                    consequent: Box::new(Value::from(1).into()),
                    alternate: Box::new(Value::from(2).into()),
                },
            },
        );

        let code = exec.disasm().collect::<Vec<_>>();
        assert!(matches!(code[0], Instruction::CopyConst { .. }));
        assert!(matches!(code[1], Instruction::JumpUnless { pos: 2, .. }));
        assert!(matches!(code[2], Instruction::CopyConst { .. }));
        assert!(matches!(code[3], Instruction::Leave { .. }));
        assert!(matches!(code[4], Instruction::CopyConst { .. }));
        assert!(matches!(code[5], Instruction::Leave { .. }));
    }

    #[test]
    fn test_tail_call() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();
        let exec = assemble(
            &mut ctx,
            Expression {
                bind: vec![Binding {
                    variable: VariableId(0),
                    kind: BindingKind::Local,
                    init: ComplexExpression::Function {
                        name: None,
                        parameters: Box::new([VariableId(1)]),
                        upvalues: Box::default(),
                        body: Box::new(
                            ComplexExpression::BinaryOp {
                                operator: BinaryOp::Mul,
                                arguments: (
                                    AtomicExpression::Value(Value::from(3)),
                                    AtomicExpression::Variable(VariableId(1)),
                                ),
                            }
                            .into(),
                        ),
                    },
                }]
                .into_boxed_slice(),
                tail: ComplexExpression::Call {
                    function: VariableId(0),
                    arguments: Box::new([Value::from(3).into()]),
                },
            },
        );

        let code = exec.disasm().collect::<Vec<_>>();
        assert!(matches!(
            code[0],
            Instruction::BinaryConst1 {
                op: BinaryOp::Mul,
                ..
            }
        ));
        assert!(matches!(code[1], Instruction::Leave { .. }));
        assert!(matches!(code[2], Instruction::MakeClosure { .. }));
        assert!(matches!(code[3], Instruction::CopyConst { .. }));
        assert!(matches!(code[4], Instruction::TailCall { .. }));
    }
}
