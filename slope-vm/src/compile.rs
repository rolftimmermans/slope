use slope_parse::{parse, Atom, AtomKind, ByteRange, SourceNode};

use slope_types::{Pair, Symbol, Value};

use crate::{
    expr::{
        AtomicExpression, BinaryOp, BindingKind, BuiltinFunc, ComplexExpression, Expression,
        ExpressionBuilder, GenVariable, UnaryOp, VariableId,
    },
    form::{
        match_binary, match_def, match_def_syntax, match_export, match_fn, match_if, match_import,
        match_let, match_let_syntax, match_unary, match_variadic, DefSyntaxMatch, SyntaxRulesMatch,
    },
    syntax::{self, Error, SyntaxRules},
    vm::AllocationContext,
    HashMap, HashSet,
};

use std::{
    borrow::Cow,
    cell::Cell,
    collections::hash_map::Entry,
    fmt::{self, Display, Formatter},
    mem::take,
    path::{Path, PathBuf},
    rc::Rc,
};

use phf::{phf_map, Map};
use strsim::jaro_winkler;

#[derive(Debug)]
pub struct SyntaxError {
    pub(crate) inner: syntax::Error,
    pub(crate) origin: ByteRange,
}

pub type SyntaxResult<T> = Result<T, SyntaxError>;

type Transform =
    for<'gc> fn(&mut Compiler<'_, 'gc>, &[SourceNode]) -> SyntaxResult<Expression<'gc>>;
type ScopedBindings<'gc> = HashMap<Symbol, Binding<'gc>>;

pub struct Module<'gc> {
    pub(crate) expr: Expression<'gc>,
    exports: ScopedBindings<'gc>,
}

pub struct Compiler<'m, 'gc> {
    ctx: &'m mut AllocationContext<'gc>,
    path: &'m Path,
    scopes: Scopes<'gc>,
    exports: HashSet<Symbol>,
    modules: HashMap<PathBuf, ScopedBindings<'gc>>,
}

struct Scopes<'gc> {
    sequence: u32,
    import_scope: Scope<'gc>,
    function_scopes: Vec<FunctionScope<'gc>>,
}

static BUILTINS: Map<&'static str, Transform> = phf_map! {
    // Builtin special forms.
    "export" => transform_export,
    "import" => transform_import,
    "begin" => transform_begin,
    "def" => transform_def,
    "def-syntax" => transform_def_syntax,
    "let" => transform_let,
    "let-syntax" => transform_let_syntax,
    "fn" => transform_fn,
    "if" => transform_if,
    "display" => transform_display,

    // Binary operators.
    "=" => |ctx, list| transform_binary_op(ctx, list, BinaryOp::IsEq),
    "<" => |ctx, list| transform_binary_op(ctx, list, BinaryOp::IsLt),
    ">" => |ctx, list| transform_binary_op(ctx, list, BinaryOp::IsGt),
    "+" => |ctx, list| transform_variadic_to_binary_op(ctx, list, BinaryOp::Add, Value::ZERO),
    "-" => |ctx, list| transform_variadic_to_binary_op(ctx, list, BinaryOp::Sub, Value::ZERO),
    "*" => |ctx, list| transform_variadic_to_binary_op(ctx, list, BinaryOp::Mul, Value::from(1)),
    "/" => |ctx, list| transform_variadic_to_binary_op(ctx, list, BinaryOp::Div, Value::from(1)),
    "%" => |ctx, list| transform_binary_op(ctx, list, BinaryOp::Rem),

    // Unary operators.
    "car" => |ctx, list| transform_unary_op(ctx, list, UnaryOp::Car),
    "cdr" => |ctx, list| transform_unary_op(ctx, list, UnaryOp::Cdr),
    "nil?" => |ctx, list| transform_unary_op(ctx, list, UnaryOp::IsNil),
    "bool?" => |ctx, list| transform_unary_op(ctx, list, UnaryOp::IsBool),
    "char?" => |ctx, list| transform_unary_op(ctx, list, UnaryOp::IsChar),
    "symbol?" => |ctx, list| transform_unary_op(ctx, list, UnaryOp::IsSymbol),
    "number?" => |ctx, list| transform_unary_op(ctx, list, UnaryOp::IsNumber),
    "string?" => |ctx, list| transform_unary_op(ctx, list, UnaryOp::IsString),
    "pair?" => |ctx, list| transform_unary_op(ctx, list, UnaryOp::IsPair),
    "vector?" => |ctx, list| transform_unary_op(ctx, list, UnaryOp::IsVector),
    "closure?" => |ctx, list| transform_unary_op(ctx, list, UnaryOp::IsClosure),
    "function?" => |ctx, list| transform_unary_op(ctx, list, UnaryOp::IsFunction),

    // Builtin functions.
    "cons" => |ctx, list| transform_builtin_func(ctx, list, BuiltinFunc::Cons),
    "list" => |ctx, list| transform_builtin_func(ctx, list, BuiltinFunc::List),
};

impl<'m, 'gc> Compiler<'m, 'gc> {
    pub(crate) fn new(ctx: &'m mut AllocationContext<'gc>, path: &'m Path) -> Self {
        let function_scopes = vec![FunctionScope::new(take(ctx.scope()))];

        Self {
            ctx,
            path,
            scopes: Scopes {
                sequence: 0,
                import_scope: Scope::default(),
                function_scopes,
            },
            exports: Default::default(),
            modules: Default::default(),
        }
    }

    pub(crate) fn compile(&mut self, nodes: &[SourceNode]) -> SyntaxResult<Expression<'gc>> {
        transform_sequence(self, nodes.iter())
    }

    pub(crate) fn scope(&mut self) -> &mut Scope<'gc> {
        debug_assert!(self.scopes.function_scopes.len() == 1);
        debug_assert!(self.scopes.function_scope().local_scopes.len() == 1);
        self.scopes.local_scope()
    }
}

const MACRO_RECURSION_LIMIT: u32 = 100;

impl Display for SyntaxError {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "{}", self.inner)
    }
}

// impl SyntaxError {
//     pub fn hint(&self) -> String {
//         match &self.inner {
//             Error::InvalidSyntax { expected } => format!("expected {}", expected),

//             Error::ExpectedList { found } => format!("found {}", found),

//             Error::ExpectedKeyword { expected, found } => {
//                 format!("expected {} but found {}", expected, found)
//             }

//             Error::ExpectedSymbol { found } => format!("found {}", found),

//             Error::ExpectedVariable { found } => {
//                 format!("keyword {} cannot be used as an expression", found)
//             }

//             Error::ExpectedClosure { found } => format!("found {}", found),

//             Error::UnboundVariable { found, similar } => {
//                 let suggestion = similar
//                     .as_ref()
//                     .map(|sym| format!(", did you mean {}?", sym))
//                     .unwrap_or_default();

//                 format!("unknown variable {}{}", found, suggestion)
//             }

//             Error::UnboundIdentifier { found, similar } => {
//                 let suggestion = similar
//                     .as_ref()
//                     .map(|sym| format!(", did you mean {}?", sym))
//                     .unwrap_or_default();

//                 format!("unknown identifier {}{}", found, suggestion)
//             }

//             Error::MacroExpansionOverflow { .. } => format!(
//                 "expansion continued for over {} iterations",
//                 MACRO_RECURSION_LIMIT
//             ),
//         }
//     }
// }

struct FunctionScope<'gc> {
    expression: ExpressionBuilder<'gc>,
    local_scopes: Vec<Scope<'gc>>,
    upvalues: HashSet<VariableId>,
}

impl<'gc> Default for FunctionScope<'gc> {
    fn default() -> Self {
        Self::new(Scope::default())
    }
}

impl<'gc> FunctionScope<'gc> {
    fn new(scope: Scope<'gc>) -> Self {
        Self {
            expression: Default::default(),
            local_scopes: vec![scope],
            upvalues: Default::default(),
        }
    }
}

#[derive(Default)]
pub struct Scope<'gc> {
    bindings: ScopedBindings<'gc>,
}

#[derive(Clone)]
enum Binding<'gc> {
    Variable {
        variable: Rc<Variable>,
        recursive: bool,
    },

    Keyword {
        syntax_rules: Rc<SyntaxRules<'gc>>,
    },

    Builtin {
        transform: Transform,
    },

    Constant {
        value: Value<'gc>,
    },
}

#[derive(Clone, Debug, Default)]
struct Variable {
    id: VariableId,
    // name: Atom,
    mutable: bool,
    finalized: Cell<bool>,
    captures: Cell<u32>,
    references: Cell<u32>,
}

macro_rules! as_string {
    ($node:expr) => {
        $node.as_string().ok_or_else(|| SyntaxError {
            inner: Error::ExpectedString {
                found: $node.as_kind_string(),
            },
            origin: $node.range(),
        })?
    };
}

macro_rules! as_symbol {
    ($node:expr) => {
        $node.as_symbol().ok_or_else(|| SyntaxError {
            inner: Error::ExpectedSymbol {
                found: $node.as_kind_string(),
            },
            origin: $node.range(),
        })?
    };
}

macro_rules! extract_symbol {
    ($context:expr, $node:expr) => {
        $context.ctx.interner().intern(as_symbol!($node).as_str())
    };
}

pub(crate) fn compile_module<'m, 'gc>(
    ctx: &'m mut AllocationContext<'gc>,
    path: &Path,
    nodes: &[SourceNode],
) -> SyntaxResult<Module<'gc>> {
    let mut context = Compiler::new(ctx, path);
    let expr = transform_sequence(&mut context, nodes.iter())?;

    let mut exports = HashMap::default();
    for export in take(&mut context.exports) {
        let binding = context.resolve(export).ok_or_else(|| SyntaxError {
            inner: Error::ExpectedVariable {
                found: context.ctx.interner().resolve(&export).to_owned(),
            },
            origin: ByteRange::default(),
        })?;

        exports.insert(export, binding);
    }

    Ok(Module { expr, exports })
}

pub(crate) fn transform_value<'gc>(
    ctx: &mut AllocationContext<'gc>,
    node: &SourceNode,
) -> SyntaxResult<Value<'gc>> {
    Ok(match node {
        SourceNode::Atom { kind, atom, .. } => {
            match kind {
                AtomKind::Bool => Value::from(atom == "#t"),
                AtomKind::Symbol => Value::from(ctx.interner().intern(atom.as_str())),
                AtomKind::Number => Value::from(atom.parse::<f64>().unwrap()), // TODO avoid panic
                AtomKind::String => Value::from(ctx.alloc(atom.to_string())),  // TODO unescape
                AtomKind::Comment => panic!("unexpected comment"),
                AtomKind::Whitespace => panic!("unexpected whitespace"),
            }
        }

        SourceNode::Cons { .. } => {
            // TODO solve this with types while keeping source node struct size small
            panic!("unexpected cons node");
        }

        SourceNode::Quoted { inner, .. } => {
            let quote = ctx.interner().intern("quote");
            let value = transform_value(ctx, inner)?;
            ctx.alloc_list([quote.into(), value].iter().cloned())
        }

        SourceNode::List { inner, .. } => {
            let mut inner = &**inner;
            let last = if let Some(SourceNode::Cons { inner: cons, .. }) = inner.last() {
                inner = &inner[..inner.len()];
                transform_value(ctx, &cons[0])?
            } else {
                Value::NIL
            };

            inner.iter().rev().try_fold(last, |list, next| {
                let pair = Pair::new(transform_value(ctx, &next)?, list);
                Ok(Value::from(ctx.alloc(pair)))
            })?
        }
    })
}

fn transform_nodes<'gc>(
    context: &mut Compiler<'_, 'gc>,
    nodes: &[SourceNode],
) -> SyntaxResult<impl DoubleEndedIterator<Item = Expression<'gc>>> {
    let vec = nodes
        .iter()
        .try_fold(Vec::with_capacity(nodes.len()), |mut exprs, node| {
            exprs.push(transform_node(context, node)?);
            Ok(exprs)
        })?;

    Ok(vec.into_iter())
}

fn transform_node<'gc>(
    context: &mut Compiler<'_, 'gc>,
    node: &SourceNode,
) -> SyntaxResult<Expression<'gc>> {
    match node {
        SourceNode::List { inner, .. } => {
            if inner.is_empty() {
                Ok(Value::NIL.into())
            } else {
                transform_apply(context, inner)
            }
        }

        SourceNode::Quoted { inner, .. } => {
            let value = transform_value(context.ctx, &inner)?;
            Ok(value.into())
        }

        SourceNode::Atom {
            kind: AtomKind::Symbol,
            atom,
            ..
        } => {
            let symbol = context.ctx.interner().intern(atom.as_str());
            if let Some(binding) = context.resolve(symbol) {
                match binding {
                    Binding::Variable { variable, .. } => Ok(variable.id.into()),

                    Binding::Constant { value } => Ok(value.into()),

                    _ => Err(SyntaxError {
                        inner: Error::ExpectedVariable {
                            found: atom.as_str().to_owned(),
                        },
                        origin: node.range(),
                    }),
                }
            } else {
                let similar = context
                    .find_similar_variable(atom)
                    .as_ref()
                    .map(|sym| context.ctx.interner().resolve(sym).to_owned());

                Err(SyntaxError {
                    inner: Error::UnboundVariable {
                        found: atom.as_str().to_owned(),
                        similar,
                    },
                    origin: node.range(),
                })
            }
        }

        _ => {
            let value = transform_value(context.ctx, &node)?;
            Ok(value.into())
        }
    }
}

fn transform_sequence<'gc, 's>(
    context: &mut Compiler<'_, 'gc>,
    mut nodes: impl Iterator<Item = &'s SourceNode>,
) -> SyntaxResult<Expression<'gc>> {
    let expr = nodes.try_fold(Value::NIL.into(), |_, node| transform_node(context, node))?;
    Ok(context.scopes.expression().append_expression(expr).take())
}

fn transform_apply<'gc>(
    context: &mut Compiler<'_, 'gc>,
    list: &[SourceNode],
) -> SyntaxResult<Expression<'gc>> {
    // Create copy-on-write struct so we can store owned version of synthetic
    // source tree during macro expansion.
    let mut list: Cow<[SourceNode]> = list.into();

    for _ in 0..MACRO_RECURSION_LIMIT {
        let node = &list[0];
        match node {
            SourceNode::Atom {
                kind: AtomKind::Symbol,
                atom,
                ..
            } => {
                let symbol = context.ctx.interner().intern(atom.as_str());
                if let Some(binding) = context.resolve(symbol) {
                    match binding {
                        Binding::Variable {
                            variable,
                            recursive,
                        } => {
                            let args = transform_nodes(context, &list[1..])?;

                            let mut builder = ExpressionBuilder::default();
                            let arguments = builder.insert_expressions(context, args);

                            if recursive {
                                builder.assign_tail(ComplexExpression::Recurse { arguments });
                            } else {
                                builder.assign_tail(ComplexExpression::Call {
                                    function: variable.id,
                                    arguments,
                                });
                            }

                            return Ok(builder.into());
                        }

                        Binding::Keyword { syntax_rules } => {
                            // Loop while this form is a macro.
                            let expanded = syntax_rules.transform(context.ctx, &list)?;

                            list = Vec::from(expanded).into();
                            continue;
                        }

                        Binding::Builtin { transform } => {
                            return transform(context, &list);
                        }

                        Binding::Constant { .. } => {
                            return Err(SyntaxError {
                                inner: Error::ExpectedClosure {
                                    //todo fix msg
                                    found: format!("{} is a constant value", atom.as_str()),
                                },
                                origin: node.range(),
                            });
                        }
                    }
                } else {
                    let similar = context
                        .find_similar_identifier(atom)
                        .as_ref()
                        .map(|sym| context.ctx.interner().resolve(sym).to_owned());

                    return Err(SyntaxError {
                        inner: Error::UnboundIdentifier {
                            found: atom.as_str().to_owned(),
                            similar,
                        },
                        origin: node.range(),
                    });
                }
            }

            SourceNode::List { .. } => {
                let args = transform_nodes(context, &list)?;

                let mut builder = ExpressionBuilder::default();
                let mut exprs = builder.insert_expressions(context, args).into_vec();

                match exprs.remove(0) {
                    AtomicExpression::Value(_value) => {
                        return Err(SyntaxError {
                            inner: Error::ExpectedClosure {
                                // found: format!("{}", value),
                                found: "todo".to_owned(),
                            },
                            origin: node.range(),
                        });
                    }

                    AtomicExpression::Variable(function) => {
                        let arguments = exprs.into_boxed_slice();
                        builder.assign_tail(ComplexExpression::Call {
                            function,
                            arguments,
                        });

                        return Ok(builder.into());
                    }
                }
            }

            _ => panic!("form not supported"),
        };
    }

    Err(SyntaxError {
        inner: Error::MacroExpansionOverflow,
        origin: list[0].range(),
    })
}

fn transform_export<'gc>(
    context: &mut Compiler<'_, 'gc>,
    list: &[SourceNode],
) -> SyntaxResult<Expression<'gc>> {
    let form = match_export(context.ctx, list)?;
    for identifier in form.identifiers.iter() {
        let identifier = extract_symbol!(context, identifier);
        context.exports.insert(identifier);
    }

    Ok(Value::NIL.into())
}

fn transform_import<'gc>(
    context: &mut Compiler<'_, 'gc>,
    list: &[SourceNode],
) -> SyntaxResult<Expression<'gc>> {
    let form = match_import(context.ctx, list)?;
    context.import(as_string!(form.path))?;

    Ok(Value::NIL.into())
}

fn transform_begin<'gc>(
    context: &mut Compiler<'_, 'gc>,
    list: &[SourceNode],
) -> SyntaxResult<Expression<'gc>> {
    transform_sequence(context, list[1..].iter())
}

fn transform_def<'gc>(
    context: &mut Compiler<'_, 'gc>,
    list: &[SourceNode],
) -> SyntaxResult<Expression<'gc>> {
    let form = match_def(context.ctx, list)?;

    if let Some((variable, init)) = bind_variable(context, form.variable, form.init)? {
        context
            .scopes
            .expression()
            .append_binding(variable.id, init, BindingKind::Local);
    }

    Ok(Value::NIL.into())
}

fn transform_let<'gc>(
    context: &mut Compiler<'_, 'gc>,
    list: &[SourceNode],
) -> SyntaxResult<Expression<'gc>> {
    let form = match_let(context.ctx, list)?;

    with_local_scope(context, |context| {
        let mut bindings = Vec::with_capacity(form.bindings.len());
        for (variable, init) in form.bindings {
            // TODO: Validate names are unique within this let form.
            if let Some(binding) = bind_variable(context, variable, init)? {
                bindings.push(binding);
            }
        }

        let expr = transform_sequence(context, form.body.iter())?;

        let mut builder = ExpressionBuilder::from(expr);
        for (variable, init) in bindings.into_iter().rev() {
            if variable.references.get() > 0 {
                builder.prepend_binding(variable.id, init, BindingKind::Local);
            } else {
                // Variable was not referenced anywhere
                // TODO: Might be nice to have a warning
            }
        }

        Ok(builder.into())
    })
}

fn bind_variable<'gc>(
    context: &mut Compiler<'_, 'gc>,
    variable: SourceNode,
    init: SourceNode,
) -> SyntaxResult<Option<(Rc<Variable>, Expression<'gc>)>> {
    let name = as_symbol!(variable);
    let variable = context.ctx.interner().intern(name.as_str());
    let declaration = context.scopes.bind_variable(variable);
    let mut init = transform_node(context, &init)?;
    declaration.finalized.set(true);

    if let (false, Some(&value)) = (declaration.mutable, init.as_value()) {
        context
            .scopes
            .local_scope()
            .bindings
            .insert(variable, Binding::Constant { value });

        Ok(None)
    } else {
        if let ComplexExpression::Function {
            name: func_name, ..
        } = &mut init.tail
        {
            *func_name = Some(name.clone());
        }

        Ok(Some((declaration, init)))
    }
}

fn transform_def_syntax<'gc>(
    context: &mut Compiler<'_, 'gc>,
    list: &[SourceNode],
) -> SyntaxResult<Expression<'gc>> {
    let DefSyntaxMatch { keyword, syntax } = match_def_syntax(context.ctx, list)?;
    bind_syntax_rules(context, keyword, syntax)?;
    Ok(Value::NIL.into())
}

fn transform_let_syntax<'gc>(
    context: &mut Compiler<'_, 'gc>,
    list: &[SourceNode],
) -> SyntaxResult<Expression<'gc>> {
    let form = match_let_syntax(context.ctx, list)?;

    with_local_scope(context, |context| {
        for (keyword, syntax) in form.bindings {
            bind_syntax_rules(context, keyword, syntax)?;
        }

        Ok(transform_sequence(context, form.body.iter())?)
    })
}

fn bind_syntax_rules<'gc>(
    context: &mut Compiler<'_, 'gc>,
    keyword: SourceNode,
    syntax: SyntaxRulesMatch,
) -> SyntaxResult<()> {
    let keyword = extract_symbol!(context, keyword);

    let mut literals = Vec::with_capacity(syntax.literals.len());
    for literal in syntax.literals {
        literals.push(extract_symbol!(context, literal));
    }

    let mut rules = SyntaxRules::new(keyword, literals.into_boxed_slice());
    for (pattern, template) in syntax.rules {
        rules.parse(context.ctx, &pattern, &template)?;
    }

    context.scopes.bind_keyword(keyword, rules);
    Ok(())
}

fn transform_if<'gc>(
    context: &mut Compiler<'_, 'gc>,
    list: &[SourceNode],
) -> SyntaxResult<Expression<'gc>> {
    let form = match_if(context.ctx, list)?;
    let test = transform_node(context, &form.test)?;

    let consequent = transform_node(context, &form.consequent)?;
    let alternate = if let Some(alternate) = &form.alternate {
        transform_node(context, alternate)?
    } else {
        Value::NIL.into()
    };

    if let Some(test) = test.as_value() {
        if test.is_false() {
            Ok(alternate)
        } else {
            Ok(consequent)
        }
    } else {
        let mut builder = ExpressionBuilder::default();
        let test = builder.insert_expression(context, test);
        builder.assign_tail(ComplexExpression::If {
            test,
            consequent: Box::new(consequent),
            alternate: Box::new(alternate),
        });

        Ok(builder.into())
    }
}

fn transform_fn<'gc>(
    context: &mut Compiler<'_, 'gc>,
    list: &[SourceNode],
) -> SyntaxResult<Expression<'gc>> {
    let form = match_fn(context.ctx, list)?;

    with_function_scope(context, |context| {
        let mut parameters = Vec::with_capacity(form.params.len());
        for param in form.params {
            let name = as_symbol!(param);
            let param = context.ctx.interner().intern(name.as_str());
            let param = context.scopes.bind_variable(param);

            param.finalized.set(true);
            parameters.push(param.id);
        }

        let body = Box::new(transform_sequence(context, form.body.iter())?);
        let upvalues = context
            .scopes
            .function_scope()
            .upvalues
            .iter()
            .cloned()
            .collect();

        Ok(ComplexExpression::Function {
            name: None,
            parameters: parameters.into_boxed_slice(),
            upvalues,
            body,
        }
        .into())
    })
}

fn transform_display<'gc>(
    context: &mut Compiler<'_, 'gc>,
    list: &[SourceNode],
) -> SyntaxResult<Expression<'gc>> {
    let arg = match_unary(context.ctx, list, "x")?;
    let arg = transform_node(context, &arg)?;

    let mut builder = ExpressionBuilder::default();
    let argument = builder.insert_expression(context, arg);
    builder.assign_tail(ComplexExpression::Display { argument });
    Ok(builder.into())
}

fn transform_unary_op<'gc>(
    context: &mut Compiler<'_, 'gc>,
    list: &[SourceNode],
    operator: UnaryOp,
) -> SyntaxResult<Expression<'gc>> {
    let arg = match_unary(context.ctx, list, "x")?;
    let arg = transform_node(context, &arg)?;

    if let Some(&value) = arg.as_value() {
        Ok(operator.apply(value).into())
    } else {
        let mut builder = ExpressionBuilder::default();
        if let AtomicExpression::Variable(argument) = builder.insert_expression(context, arg) {
            builder.assign_tail(ComplexExpression::UnaryOp { operator, argument });
        } else {
            unreachable!();
        }

        Ok(builder.into())
    }
}

fn transform_binary_op<'gc>(
    context: &mut Compiler<'_, 'gc>,
    list: &[SourceNode],
    operator: BinaryOp,
) -> SyntaxResult<Expression<'gc>> {
    let (arg1, arg2) = match_binary(context.ctx, list, "x", "y")?;

    let arg1 = transform_node(context, &arg1)?;
    let arg2 = transform_node(context, &arg2)?;

    if let (Some(&val1), Some(&val2)) = (arg1.as_value(), arg2.as_value()) {
        Ok(operator.apply(val1, val2).into())
    } else {
        let mut builder = ExpressionBuilder::default();
        let arguments = (
            builder.insert_expression(context, arg1),
            builder.insert_expression(context, arg2),
        );

        builder.assign_tail(ComplexExpression::BinaryOp {
            operator,
            arguments,
        });

        Ok(builder.into())
    }
}

fn transform_variadic_to_binary_op<'gc>(
    context: &mut Compiler<'_, 'gc>,
    list: &[SourceNode],
    operator: BinaryOp,
    unit: Value<'gc>,
) -> SyntaxResult<Expression<'gc>> {
    let args = match_variadic(context.ctx, list, "x")?;
    let mut args = transform_nodes(context, &args)?;

    let mut builder = ExpressionBuilder::default();
    if let Some(mut expr) = args.next() {
        for next in args {
            if let (Some(&val1), Some(&val2)) = (expr.as_value(), next.as_value()) {
                expr = operator.apply(val1, val2).into();
            } else {
                expr = ComplexExpression::BinaryOp {
                    operator,
                    arguments: (
                        builder.insert_expression(context, expr),
                        builder.insert_expression(context, next),
                    ),
                }
                .into();
            }
        }

        builder.append_expression(expr);
        Ok(builder.into())
    } else {
        Ok(unit.into())
    }
}

fn transform_builtin_func<'gc>(
    context: &mut Compiler<'_, 'gc>,
    list: &[SourceNode],
    function: BuiltinFunc,
) -> SyntaxResult<Expression<'gc>> {
    let args = match_variadic(context.ctx, list, "x")?;
    let args = transform_nodes(context, &args)?;

    let mut builder = ExpressionBuilder::default();
    let arguments = builder.insert_expressions(context, args);
    builder.assign_tail(ComplexExpression::CallBuiltin {
        function,
        arguments,
    });

    Ok(builder.into())
}

fn with_local_scope<'gc, T>(
    context: &mut Compiler<'_, 'gc>,
    fun: impl FnOnce(&mut Compiler<'_, 'gc>) -> T,
) -> T {
    context
        .scopes
        .function_scope()
        .local_scopes
        .push(Scope::default());

    let res = fun(context);
    context.scopes.function_scope().local_scopes.pop();
    res
}

fn with_function_scope<'gc, T>(
    context: &mut Compiler<'_, 'gc>,
    fun: impl FnOnce(&mut Compiler<'_, 'gc>) -> T,
) -> T {
    context
        .scopes
        .function_scopes
        .push(FunctionScope::default());

    let res = fun(context);
    context.scopes.function_scopes.pop();
    res
}

impl GenVariable for Compiler<'_, '_> {
    fn gen_variable(&mut self) -> VariableId {
        self.scopes.gen_variable()
    }
}

impl GenVariable for Scopes<'_> {
    fn gen_variable(&mut self) -> VariableId {
        let id = self.sequence;
        self.sequence += 1;
        VariableId(id)
    }
}

impl<'gc> Compiler<'_, 'gc> {
    fn import(&mut self, path: &str) -> SyntaxResult<()> {
        // TODO: Is this the right place for caching?
        match self.modules.entry(self.path.join(path)) {
            Entry::Occupied(entry) => {
                self.scopes
                    .import_scope
                    .bindings
                    .extend(entry.get().clone());
                Ok(())
            }

            Entry::Vacant(entry) => {
                let path = entry.key();
                let source = self.ctx.loader().read(path).unwrap();
                let node = parse(&source).collect::<Result<Vec<_>, _>>().unwrap();
                let module = compile_module(self.ctx, path, &node)?;

                self.scopes.expression().append_expression(module.expr);
                self.scopes
                    .import_scope
                    .bindings
                    .extend(entry.insert(module.exports).clone());

                Ok(())
            }
        }
    }

    fn resolve(&mut self, symbol: Symbol) -> Option<Binding<'gc>> {
        for scope in self.scopes.function_scope().local_scopes.iter().rev() {
            if let Some(binding) = scope.bindings.get(&symbol) {
                let binding = binding.clone();
                if let Binding::Variable { variable, .. } = &binding {
                    if !variable.finalized.get() {
                        continue;
                    }

                    variable.references.set(variable.references.get() + 1);
                }

                return Some(binding);
            }
        }

        for (level, function_scope) in self.scopes.function_scopes.iter().enumerate().rev().skip(1)
        {
            for scope in function_scope.local_scopes.iter().rev() {
                if let Some(binding) = scope.bindings.get(&symbol) {
                    let mut binding = binding.clone();
                    if let Binding::Variable {
                        variable,
                        recursive,
                    } = &mut binding
                    {
                        variable.references.set(variable.references.get() + 1);
                        variable.captures.set(variable.captures.get() + 1);

                        if level + 2 == self.scopes.function_scopes.len()
                            && !variable.finalized.get()
                        {
                            *recursive = true;
                        } else {
                            for function_scope in
                                self.scopes.function_scopes[level + 1..].iter_mut()
                            {
                                function_scope.upvalues.insert(variable.id);
                            }
                        }
                    }

                    return Some(binding);
                }
            }
        }

        if let Some(binding) = self.scopes.import_scope.bindings.get(&symbol) {
            return Some(binding.clone());
        }

        if let Some(&transform) = BUILTINS.get(self.ctx.interner().resolve(&symbol)) {
            return Some(Binding::Builtin { transform });
        }

        None
    }

    fn find_similar_identifier(&mut self, found: &Atom) -> Option<Symbol> {
        let mut suggestion = (0.9, None);

        for &existing in self.scopes.each_identifier() {
            let score = jaro_winkler(found, self.ctx.interner().resolve(&existing));
            if score > suggestion.0 {
                suggestion = (score, Some(existing))
            }
        }

        suggestion.1
    }

    fn find_similar_variable(&mut self, found: &Atom) -> Option<Symbol> {
        let mut suggestion = (0.9, None);

        for &existing in self.scopes.each_variable() {
            let score = jaro_winkler(found, self.ctx.interner().resolve(&existing));
            if score > suggestion.0 {
                suggestion = (score, Some(existing))
            }
        }

        suggestion.1
    }
}

impl<'gc> Scopes<'gc> {
    fn expression(&mut self) -> &mut ExpressionBuilder<'gc> {
        &mut self.function_scope().expression
    }

    fn function_scope(&mut self) -> &mut FunctionScope<'gc> {
        self.function_scopes
            .last_mut()
            .expect("missing function scope")
    }

    fn local_scope(&mut self) -> &mut Scope<'gc> {
        self.function_scope()
            .local_scopes
            .last_mut()
            .expect("missing local scope")
    }

    fn each_identifier(&self) -> impl Iterator<Item = &Symbol> {
        self.function_scopes
            .iter()
            .flat_map(|function_scope| function_scope.local_scopes.iter())
            .flat_map(|scope| scope.bindings.keys())
    }

    fn each_variable(&self) -> impl Iterator<Item = &Symbol> {
        self.function_scopes
            .iter()
            .flat_map(|function_scope| function_scope.local_scopes.iter())
            .flat_map(|scope| {
                scope.bindings.iter().filter_map(|(identifier, binding)| {
                    if let Binding::Variable { .. } | Binding::Constant { .. } = binding {
                        Some(identifier)
                    } else {
                        None
                    }
                })
            })
    }

    fn bind_variable(&mut self, symbol: Symbol) -> Rc<Variable> {
        // assert!(!name.is_empty());

        let variable = Rc::new(Variable {
            id: self.gen_variable(),
            // name,
            ..Default::default()
        });

        self.local_scope().bindings.insert(
            symbol,
            Binding::Variable {
                variable: variable.clone(),
                recursive: false,
            },
        );

        variable
    }

    fn bind_keyword(
        &mut self,
        symbol: Symbol,
        syntax_rules: SyntaxRules<'gc>,
    ) -> Rc<SyntaxRules<'gc>> {
        let syntax_rules = Rc::new(syntax_rules);

        self.local_scope().bindings.insert(
            symbol,
            Binding::Keyword {
                syntax_rules: syntax_rules.clone(),
            },
        );

        syntax_rules
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{expr::Binding, vm::VirtualMachine};
    use slope_parse::parse;
    use std::env::current_dir;

    fn compile_str<'gc>(
        ctx: &mut AllocationContext<'gc>,
        input: &str,
    ) -> Result<Expression<'gc>, SyntaxError> {
        let dir = current_dir().unwrap();
        let mut compiler = Compiler::new(ctx, &dir);
        compiler.compile(&[parse(input).next().unwrap().unwrap()])
    }

    #[test]
    fn test_transform_trivial_exprs() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();

        assert_eq!(compile_str(&mut ctx, &"1").unwrap(), Value::from(1).into());

        assert_eq!(
            compile_str(&mut ctx, &"\"foo\"").unwrap(),
            Value::from(ctx.alloc("foo".to_owned())).into()
        );

        assert_eq!(
            compile_str(&mut ctx, &"'bar").unwrap(),
            Value::from(ctx.interner().intern("bar")).into()
        );
    }

    #[test]
    fn test_transform_let() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();

        assert_eq!(
            compile_str(&mut ctx, &"(let ((a 1)) a)").unwrap(),
            Expression {
                bind: Box::new([]),
                tail: Value::from(1.0).into(),
            }
        );
    }

    #[test]
    fn test_transform_let_multi() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();

        assert_eq!(
            compile_str(&mut ctx, &"(let ((a 1) (b 2)) a)").unwrap(),
            Expression {
                bind: Box::new([]),
                tail: Value::from(1.0).into(),
            }
        );
    }

    #[test]
    fn test_transform_let_alias() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();

        assert_eq!(
            compile_str(&mut ctx, &"(let ((a 1) (b a)) b)").unwrap(),
            Expression {
                bind: Box::new([]),
                tail: Value::from(1.0).into(),
            }
        );
    }

    #[test]
    fn test_transform_let_nested() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();

        assert_eq!(
            compile_str(&mut ctx, &"(let ((a (let ((b 1)) b))) a)").unwrap(),
            Expression {
                bind: Box::new([]),
                tail: Value::from(1.0).into(),
            }
        );
    }

    #[test]
    fn test_transform_def() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();

        assert_eq!(
            compile_str(&mut ctx, &"(begin (def a 1) a)").unwrap(),
            Expression {
                bind: Box::new([]),
                tail: Value::from(1.0).into(),
            }
        );
    }

    #[test]
    fn test_transform_def_multi() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();

        assert_eq!(
            compile_str(&mut ctx, &"(begin (def a 1) (def b 2) a)").unwrap(),
            Expression {
                bind: Box::new([]),
                tail: Value::from(1.0).into(),
            }
        );
    }

    #[test]
    fn test_transform_let_syntax() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();

        assert_eq!(
            compile_str(
                &mut ctx,
                "\
                (let-syntax \
                ((my-let \
                    (syntax-rules () \
                    ((my-let var init body) (let ((var init)) body)) \
                    ))) \
                (my-let a 1 a))"
            )
            .unwrap(),
            Expression {
                bind: Box::new([]),
                tail: Value::from(1.0).into(),
            }
        );
    }

    #[test]
    fn test_transform_begin() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();

        assert_eq!(
            compile_str(&mut ctx, &"(begin (+ 1 2) 3)").unwrap(),
            Expression {
                bind: Box::new([]),
                tail: Value::from(3.0).into(),
            }
        );
    }

    #[test]
    fn test_transform_if() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();
        let no = ctx.interner().intern("no");

        assert_eq!(
            compile_str(&mut ctx, &"(if (= 1 2) 'yes 'no)").unwrap(),
            Expression {
                bind: Box::new([]),
                tail: Value::from(no).into(),
            }
        );
    }

    // TODO
    // #[test]
    // fn test_transform_apply_ops() {
    //     let mut vm = VirtualMachine::default();
    //     let mut ctx = vm.mutate_alloc();

    //     assert_eq!(
    //         compile_str(&mut ctx, "(car (cons 1 2))").unwrap(),
    //         Expression {
    //             bind: Box::new([]),
    //             tail: Value::from(1.0).into(),
    //         }
    //     );
    // }

    #[test]
    fn test_transform_apply_func() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();

        assert_eq!(
            compile_str(
                &mut ctx,
                "(let ((x (fn (a b) (+ a b)))) \
                   (x 2 3))"
            )
            .unwrap(),
            Expression {
                bind: Box::new([Binding {
                    variable: VariableId(0),
                    kind: BindingKind::Local,
                    init: ComplexExpression::Function {
                        name: Some("x".into()),
                        parameters: Box::new([VariableId(1), VariableId(2),]),
                        upvalues: Box::new([]),
                        body: Box::new(
                            ComplexExpression::BinaryOp {
                                operator: BinaryOp::Add,
                                arguments: (VariableId(1).into(), VariableId(2).into(),),
                            }
                            .into()
                        ),
                    },
                },]),
                tail: ComplexExpression::Call {
                    function: VariableId(0),
                    arguments: Box::new([Value::from(2).into(), Value::from(3).into(),]),
                },
            }
        );
    }

    #[test]
    fn test_transform_apply_recursive_func() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();

        assert_eq!(
            compile_str(
                &mut ctx,
                "(let ((x (fn (a b) (x a b)))) \
                   (x 2 3))"
            )
            .unwrap(),
            Expression {
                bind: Box::new([Binding {
                    variable: VariableId(0),
                    kind: BindingKind::Local,
                    init: ComplexExpression::Function {
                        name: Some("x".into()),
                        parameters: Box::new([VariableId(1), VariableId(2),]),
                        upvalues: Box::new([]),
                        body: Box::new(
                            ComplexExpression::Recurse {
                                arguments: Box::new([VariableId(1).into(), VariableId(2).into()]),
                            }
                            .into()
                        ),
                    },
                },]),
                tail: ComplexExpression::Call {
                    function: VariableId(0),
                    arguments: Box::new([Value::from(2).into(), Value::from(3).into(),]),
                },
            }
        );
    }

    #[test]
    fn test_transform_apply_inner_recursive_func() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();

        assert_eq!(
            compile_str(
                &mut ctx,
                "(let ((x (fn (a b)
                            (def y (fn (a b) (x a b)))
                            (y a b)))) \
                   (x 2 3))"
            )
            .unwrap(),
            Expression {
                bind: Box::new([Binding {
                    variable: VariableId(0),
                    kind: BindingKind::Local,
                    init: ComplexExpression::Function {
                        name: Some("x".into()),
                        parameters: Box::new([VariableId(1), VariableId(2),]),
                        upvalues: Box::new([VariableId(0)]),
                        body: Box::new(Expression {
                            bind: Box::new([Binding {
                                variable: VariableId(3),
                                kind: BindingKind::Local,
                                init: ComplexExpression::Function {
                                    name: Some("y".into()),
                                    parameters: Box::new([VariableId(4), VariableId(5),]),
                                    upvalues: Box::new([VariableId(0)]),
                                    body: Box::new(
                                        ComplexExpression::Call {
                                            function: VariableId(0),
                                            arguments: Box::new([
                                                VariableId(4).into(),
                                                VariableId(5).into()
                                            ]),
                                        }
                                        .into()
                                    ),
                                }
                            }]),
                            tail: ComplexExpression::Call {
                                function: VariableId(3),
                                arguments: Box::new([VariableId(1).into(), VariableId(2).into()]),
                            },
                        }),
                    },
                },]),
                tail: ComplexExpression::Call {
                    function: VariableId(0),
                    arguments: Box::new([Value::from(2).into(), Value::from(3).into(),]),
                },
            }
        );
    }

    #[test]
    fn test_transform_export() {
        let mut vm = VirtualMachine::default();
        let mut ctx = vm.mutate_alloc();

        assert_eq!(
            compile_str(&mut ctx, "(export x) (def x 4)").unwrap(),
            Expression {
                bind: Box::new([]),
                tail: Value::NIL.into(),
            }
        );
    }
}
