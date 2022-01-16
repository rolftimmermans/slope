use slope_parse::{Atom, AtomKind, SourceNode};

use slope_types::{Symbol, Value};

use std::fmt::{self, Display, Formatter};

use crate::{
    compile::{transform_value, SyntaxError, SyntaxResult},
    vm::AllocationContext,
    HashMap,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    InvalidSyntax {
        expected: String,
    },
    ExpectedList {
        found: String,
    },
    ExpectedKeyword {
        found: String,
        expected: String,
    },
    ExpectedString {
        found: String,
    },
    ExpectedSymbol {
        found: String,
    },
    ExpectedVariable {
        found: String,
    },
    ExpectedClosure {
        found: String,
    },
    UnboundVariable {
        found: String,
        similar: Option<String>,
    },
    UnboundIdentifier {
        found: String,
        similar: Option<String>,
    },
    MacroExpansionOverflow,
}

#[derive(Debug)]
pub struct SyntaxRules<'gc> {
    keyword: Symbol,
    literals: Box<[Symbol]>,
    rules: Vec<(ListPattern<'gc>, ListTemplate)>,
}

#[derive(Default, Debug, PartialEq, Eq)]
pub struct ListPattern<'gc> {
    pub patterns: Box<[Pattern<'gc>]>,
}

#[derive(Default, Debug, PartialEq, Eq)]
pub struct ListTemplate {
    pub template: Box<[Template]>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Pattern<'gc> {
    Ignored,
    Capture(Atom), // TODO use interned string or symbol
    Literal(Value<'gc>),
    List(ListPattern<'gc>),
    Repeat(Box<Pattern<'gc>>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Template {
    Replace(Atom), // TODO use interned string or symbol
    Literal(SourceNode),
    List(ListTemplate),
    Repeat(Box<Template>),
}

#[derive(Debug)]
pub struct Matches {
    matches: HashMap<Atom, Match>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Match {
    Repeating(Vec<Match>),
    Single(SourceNode),
}

impl<'gc> From<ListPattern<'gc>> for Pattern<'gc> {
    fn from(list: ListPattern<'gc>) -> Self {
        Pattern::List(list)
    }
}

impl<'gc> SyntaxRules<'gc> {
    pub fn new(keyword: Symbol, literals: Box<[Symbol]>) -> Self {
        Self {
            keyword,
            literals,
            rules: Default::default(),
        }
    }

    pub fn parse(
        &mut self,
        ctx: &mut AllocationContext<'gc>,
        pattern: &SourceNode,
        template: &SourceNode,
    ) -> SyntaxResult<()> {
        let pattern = pattern.as_list().ok_or_else(|| SyntaxError {
            inner: Error::ExpectedList {
                found: pattern.as_kind_string(),
            },
            origin: pattern.range(),
        })?;

        let template = template.as_list().ok_or_else(|| SyntaxError {
            inner: Error::ExpectedList {
                found: template.as_kind_string(),
            },
            origin: template.range(),
        })?;

        let mut vars = vec![];
        let pair = (
            self.parse_pattern(ctx, pattern, &mut vars)?,
            self.parse_template(ctx, template, &vars, 0)?,
        );

        self.rules.push(pair);
        Ok(())
    }

    pub fn transform(
        &self,
        ctx: &mut AllocationContext<'gc>,
        list: &[SourceNode],
    ) -> SyntaxResult<Box<[SourceNode]>> {
        let mut error = None;

        for (pattern, template) in &self.rules {
            match pattern.matches(ctx, list) {
                Ok(res) => return Ok(template.expand(res)),
                Err(err) => {
                    if error.is_none() {
                        error.replace(err);
                    }
                }
            }
        }

        Err(error.expect("no rules defined"))
    }

    fn parse_pattern(
        &self,
        ctx: &mut AllocationContext<'gc>,
        nodes: &[SourceNode],
        vars: &mut Vec<(u32, Atom)>,
    ) -> SyntaxResult<ListPattern<'gc>> {
        if let SourceNode::Atom {
            kind: AtomKind::Symbol,
            atom,
            ..
        } = &nodes[0]
        {
            if ctx.interner().get(atom.as_str()) != Some(self.keyword) && atom.as_str() != "_" {
                return Err(SyntaxError {
                    inner: Error::ExpectedKeyword {
                        expected: format!("{} or _", ctx.interner().resolve(&self.keyword)),
                        found: format!("{}", atom),
                    },
                    origin: nodes[0].range(),
                });
            }
        }

        let mut pattern = self.parse_inner_pattern(ctx, nodes, vars, 0)?;
        pattern.patterns[0] = Pattern::Literal(self.keyword.clone().into());
        Ok(pattern)
    }

    fn parse_inner_pattern(
        &self,
        ctx: &mut AllocationContext<'gc>,
        nodes: &[SourceNode],
        vars: &mut Vec<(u32, Atom)>,
        repeat_depth: u32,
    ) -> SyntaxResult<ListPattern<'gc>> {
        let mut patterns = vec![];
        let mut nodes = nodes.iter().peekable();

        while let Some(node) = nodes.next() {
            let mut repeating = false;

            if let Some(SourceNode::Atom {
                kind: AtomKind::Symbol,
                atom,
                ..
            }) = nodes.peek()
            {
                if atom == "..." {
                    repeating = true;
                }
            }

            let item = match node {
                SourceNode::Atom {
                    kind: AtomKind::Symbol,
                    atom,
                    ..
                } if atom == "_" => Pattern::Ignored,

                SourceNode::Atom {
                    kind: AtomKind::Symbol,
                    atom,
                    ..
                } => {
                    if let Some(symbol) = self
                        .literals
                        .iter()
                        .find(|&&lit| Some(lit) == ctx.interner().get(atom.as_str()))
                    {
                        Pattern::Literal(symbol.clone().into())
                    } else {
                        vars.push((repeat_depth + repeating as u32, atom.clone()));
                        Pattern::Capture(atom.to_owned())
                    }
                }

                SourceNode::List { inner, .. } => Pattern::List(self.parse_inner_pattern(
                    ctx,
                    inner,
                    vars,
                    repeat_depth + repeating as u32,
                )?),

                SourceNode::Atom { .. } | SourceNode::Quoted { .. } => {
                    Pattern::Literal(transform_value(ctx, node)?)
                } // todo fix error type here

                _ => panic!("unexpected node type"),
            };

            if repeating {
                patterns.push(Pattern::Repeat(Box::new(item)));
                nodes.next();
            } else {
                patterns.push(item);
            }
        }

        Ok(ListPattern {
            patterns: patterns.into_boxed_slice(),
        })
    }

    fn parse_template(
        &self,
        ctx: &mut AllocationContext<'gc>,
        nodes: &[SourceNode],
        vars: &[(u32, Atom)],
        repeat_depth: u32,
    ) -> SyntaxResult<ListTemplate> {
        let mut template = vec![];

        let mut nodes = nodes.iter().peekable();
        while let Some(node) = nodes.next() {
            let mut repeating = false;

            if let Some(SourceNode::Atom {
                kind: AtomKind::Symbol,
                atom,
                ..
            }) = nodes.peek()
            {
                if atom == "..." {
                    repeating = true;
                }
            }

            let item = match node {
                SourceNode::Atom {
                    kind: AtomKind::Symbol,
                    atom,
                    ..
                } => {
                    if let Some(&(depth, _)) = vars.iter().find(|(_, var)| var == atom) {
                        if repeat_depth + repeating as u32 == depth {
                            Template::Replace(atom.to_owned())
                        } else {
                            panic!("invalid depth")
                        }
                    } else {
                        Template::Literal(node.without_location()) // todo this is not right, hygiene!
                    }
                }

                SourceNode::List { inner, .. } => Template::List(self.parse_template(
                    ctx,
                    inner,
                    vars,
                    repeat_depth + repeating as u32,
                )?),

                SourceNode::Atom { .. } | SourceNode::Quoted { .. } => {
                    Template::Literal(node.without_location())
                }

                _ => panic!("unexpected node type"),
            };

            if repeating {
                template.push(Template::Repeat(Box::new(item)));
                nodes.next();
            } else {
                template.push(item);
            }
        }

        Ok(ListTemplate {
            template: template.into_boxed_slice(),
        })
    }
}

impl<'gc> ListPattern<'gc> {
    pub fn matches(
        &self,
        ctx: &mut AllocationContext<'gc>,
        list: &[SourceNode],
    ) -> SyntaxResult<Matches> {
        let mut matches = HashMap::default();
        if self.extract_matches(ctx, list, &mut matches, &[])? {
            Ok(Matches { matches })
        } else {
            Err(SyntaxError {
                inner: Error::InvalidSyntax {
                    expected: self.to_string(),
                },
                origin: list[0].range(),
            })
        }
    }

    fn extract_matches(
        &self,
        ctx: &mut AllocationContext<'gc>,
        vals: &[SourceNode],
        matches: &mut HashMap<Atom, Match>,
        repeats: &[u32],
    ) -> SyntaxResult<bool> {
        let pats = self.patterns.as_ref();

        let mut p = 0;
        let mut v = 0;

        // We need a pattern, but there might be no more values; which can
        // match a repeating pattern.
        while p < pats.len() {
            let pat = &pats[p];

            if let Pattern::Repeat(rep) = pat {
                // Repeat pattern until there are JUST enough values left
                // for any subsequent patterns. Might be 0 repetitions.
                let mut repeats = repeats.to_owned();
                let depth = repeats.len();
                repeats.push(0);

                while !vals.is_empty() && vals.len() - v >= pats.len() - p {
                    let val = &vals[v];

                    if !rep.extract_single(ctx, val, matches, &repeats)? {
                        return Ok(false);
                    }

                    // Next value
                    v += 1;
                    repeats[depth] += 1;
                }

                p += 1; // Next pattern
            } else {
                // We need a value to be present.
                if v < vals.len() {
                    let val = &vals[v];
                    if !pat.extract_single(ctx, val, matches, repeats)? {
                        return Ok(false);
                    }
                }

                v += 1; // Next value
                p += 1; // Next pattern
            }
        }

        // println!("d {} {} {} {}", p, pats.len(), v, vals.len());
        // println!("{:?}", pats);

        // All patterns and values should have been matched by now.
        Ok(p == pats.len() && v == vals.len())
    }
}

impl<'gc> Pattern<'gc> {
    fn extract_single(
        &self,
        ctx: &mut AllocationContext<'gc>,
        node: &SourceNode,
        matches: &mut HashMap<Atom, Match>,
        repeats: &[u32],
    ) -> SyntaxResult<bool> {
        match self {
            Pattern::Ignored => {
                // Always matches.
                Ok(true)
            }

            Pattern::Capture(var) => {
                // Always matches a value, bind variable.
                // println!("matching identifier {:?} -> {:?}", var, val);
                create_match(matches, var.clone(), repeats, Match::Single(node.clone()));
                Ok(true)
            }

            Pattern::Literal(pat) => {
                // Matches if values are equal.
                Ok(transform_value(ctx, &node)? == *pat) // todo, what about symbols, rounding?
            }

            Pattern::List(list) => {
                // Match an inner list.
                match node {
                    SourceNode::List { inner, .. } => {
                        list.extract_matches(ctx, &inner, matches, repeats)
                    }

                    _ => Ok(false),
                }
            }

            Pattern::Repeat(..) => unreachable!("invalid pattern"),
        }
    }
}

impl Display for Error {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Error::InvalidSyntax { .. } => write!(fmt, "invalid syntax"),
            Error::ExpectedList { .. } => write!(fmt, "expected list"),
            Error::ExpectedKeyword { .. } => write!(fmt, "expected keyword"),
            Error::ExpectedString { .. } => write!(fmt, "expected string"),
            Error::ExpectedSymbol { .. } => write!(fmt, "expected symbol"),
            Error::ExpectedVariable { .. } => write!(fmt, "expected variable"),
            Error::ExpectedClosure { .. } => write!(fmt, "expected closure"),
            Error::UnboundVariable { .. } => write!(fmt, "unbound variable"),
            Error::UnboundIdentifier { .. } => write!(fmt, "unbound identifier"),
            Error::MacroExpansionOverflow { .. } => write!(fmt, "macro expansion overflow"),
        }
    }
}

macro_rules! format_list {
    ($fmt:expr, $pat:literal, $iter:expr) => {{
        format_list!($fmt, "(", $pat, $iter, ")")
    }};

    ($fmt:expr, $pat:literal, $iter:expr, $last:expr) => {{
        format_list!($fmt, "(", $pat, $iter, concat!(" . ", $pat, ")"), $last)
    }};

    ($fmt:expr, $open:literal, $pat:literal, $iter:expr, $close:expr $( , $last:expr )*) => {{
        write!($fmt, $open)?;

        let mut values = $iter;
        if let Some(first) = values.next() {
            write!($fmt, $pat, first)?;

            for next in values {
                write!($fmt, concat!(" ", $pat), next)?;
            }
        }

        write!($fmt, $close, $( $last )*)
    }};
}

impl<'gc> Display for ListPattern<'gc> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        format_list!(fmt, "{}", self.patterns.iter())
    }
}

impl<'gc> Display for Pattern<'gc> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Pattern::Ignored => write!(fmt, "_"),
            Pattern::Capture(var) => write!(fmt, "<{}>", var),
            Pattern::Literal(node) => write!(fmt, "{:?}", node),
            Pattern::List(list) => write!(fmt, "{}", list),
            Pattern::Repeat(inner) => write!(fmt, "{} ...", inner),
        }
    }
}

impl ListTemplate {
    fn expand(&self, matches: Matches) -> Box<[SourceNode]> {
        self.expand_matches(&matches.matches, &[])
    }

    fn expand_matches(&self, matches: &HashMap<Atom, Match>, repeats: &[u32]) -> Box<[SourceNode]> {
        let mut vals = vec![];
        let tpls = self.template.as_ref();

        let mut t = 0;
        while t < tpls.len() {
            let tpl = &tpls[t];
            // println!("{:?}", tpl);

            if let Template::Repeat(_rep) = tpl {
                let mut repeats = repeats.to_owned();
                let _depth = repeats.len();
                repeats.push(0);

                todo!()
            // while vals.len() - v >= pats.len() - p {
            //     let val = &vals[v];

            //     vals.push(tpl.expand_single(matches, &repeats));

            //     // Next value
            //     v += 1;
            //     repeats[depth] += 1;
            // }
            } else {
                vals.push(tpl.expand_single(matches, repeats));
                t += 1;
            }
        }

        vals.into_boxed_slice()
    }
}

impl Template {
    fn expand_single(&self, matches: &HashMap<Atom, Match>, repeats: &[u32]) -> SourceNode {
        match self {
            Template::Replace(var) => expand_match(matches, var, repeats),

            Template::Literal(val) => val.clone(),

            Template::List(list) => SourceNode::List {
                inner: list.expand_matches(matches, repeats),
                range: Default::default(),
            },

            Template::Repeat(..) => unreachable!("invalid template"),
        }
    }
}

impl Matches {
    pub fn get_single(&mut self, var: impl AsRef<str>) -> Option<SourceNode> {
        self.matches
            .remove(var.as_ref())
            .map(Match::into_single)
            .flatten()
    }

    pub fn get_repeating(&mut self, var: impl AsRef<str>) -> Option<impl Iterator<Item = Match>> {
        self.matches
            .remove(var.as_ref())
            .unwrap_or_else(|| Match::Repeating(vec![]))
            .into_repeating()
    }
}

impl Match {
    pub fn into_single(self) -> Option<SourceNode> {
        if let Match::Single(node) = self {
            Some(node)
        } else {
            None
        }
    }

    pub fn into_repeating(self) -> Option<impl Iterator<Item = Match>> {
        if let Match::Repeating(inner) = self {
            Some(inner.into_iter())
        } else {
            None
        }
    }
}

fn create_match(table: &mut HashMap<Atom, Match>, var: Atom, repeats: &[u32], insert: Match) {
    if repeats.is_empty() {
        table.entry(var).or_insert(insert);
        return;
    }

    let mut matx = table.entry(var).or_insert_with(|| Match::Repeating(vec![]));
    for (i, &repeat) in repeats.iter().enumerate() {
        if let Match::Repeating(inner) = matx {
            if i == repeats.len() - 1 {
                debug_assert!(inner.len() == repeat as usize);
                inner.push(insert);
                return;
            } else {
                if inner.len() == repeat as usize {
                    inner.push(Match::Repeating(vec![]));
                }

                debug_assert!(inner.len() > repeat as usize);
                matx = &mut inner[repeat as usize];
            }
        } else {
            panic!("expected repeating matches")
        }
    }
}

fn expand_match(table: &HashMap<Atom, Match>, var: &Atom, repeats: &[u32]) -> SourceNode {
    if repeats.is_empty() {
        if let Match::Single(node) = table.get(var).unwrap() {
            return node.clone();
        } else {
            panic!("expected single match");
        }
    }

    let mut matx = table.get(var).unwrap();
    for (i, &repeat) in repeats.iter().enumerate() {
        if let Match::Repeating(inner) = matx {
            if i == repeats.len() - 1 {
                if let Match::Single(node) = &inner[repeat as usize] {
                    return node.clone();
                } else {
                    panic!("expected single match");
                }
            } else {
                matx = &inner[repeat as usize];
            }
        } else {
            panic!("expected repeating matches")
        }
    }

    unreachable!()
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     use slope_parse::parse;

//     // macro_rules! repeat_template {
//     //     ( $exp:expr ) => {
//     //         Template::Repeat(Box::new($exp.into()))
//     //     };
//     // }

//     macro_rules! list_template {
//         ( $( $exp:expr, )+ ) => {
//             ListTemplate {
//                 template: vec![
//                     $( $exp.into(), )+
//                 ].into_boxed_slice()
//             }
//         };
//     }

//     fn parse_expr(input: &str) -> SourceNode {
//         parse(input).next().unwrap().unwrap()
//     }

//     fn parse_list(input: &str) -> Box<[SourceNode]> {
//         match parse(input).next().unwrap().unwrap() {
//             SourceNode::List { inner, .. } => inner,
//             _ => panic!("not a list"),
//         }
//     }

//     #[test]
//     fn test_simple_repeating() {
//         let mut vm = VirtualMachine::default();
//         let pattern = list_pattern![repeat_pattern!(Pattern::Capture("rep".into())),];
//         let list = parse_list("()");
//         let res = pattern.matches(&mut vm, &list).unwrap();
//         assert_eq!(res.matches.get("rep"), None);

//         let list = parse_list("(1 2 3)");
//         let res = pattern.matches(&mut vm, &list).unwrap();

//         assert_eq!(
//             *res.matches.get("rep").unwrap(),
//             Match::Repeating(vec![
//                 Match::Single(SourceNode::Atom {
//                     kind: AtomKind::Number,
//                     atom: "1".into(),
//                     pos: 1.into(),
//                 }),
//                 Match::Single(SourceNode::Atom {
//                     kind: AtomKind::Number,
//                     atom: "2".into(),
//                     pos: 3.into(),
//                 }),
//                 Match::Single(SourceNode::Atom {
//                     kind: AtomKind::Number,
//                     atom: "3".into(),
//                     pos: 5.into(),
//                 })
//             ])
//         );
//     }

//     #[test]
//     fn test_custom_pattern_expand() {
//         let mut vm = VirtualMachine::default();
//         let pattern = list_pattern![
//             Pattern::Ignored,
//             Pattern::Capture("var1".into()),
//             Pattern::Capture("var2".into()),
//         ];

//         let list = parse_list("(lol 3.14 6.28)");
//         let res = pattern.matches(&mut vm, &list).unwrap();

//         let pattern = list_template![
//             Template::Literal(SourceNode::synth_atom(AtomKind::String, "hello world")),
//             Template::Replace("var2".into()),
//             Template::Replace("var1".into()),
//         ];

//         assert_eq!(
//             pattern.expand(res),
//             vec![
//                 SourceNode::Atom {
//                     kind: AtomKind::String,
//                     atom: "hello world".into(),
//                     pos: Default::default(),
//                 },
//                 SourceNode::Atom {
//                     kind: AtomKind::Number,
//                     atom: "6.28".into(),
//                     pos: 10.into(),
//                 },
//                 SourceNode::Atom {
//                     kind: AtomKind::Number,
//                     atom: "3.14".into(),
//                     pos: 5.into(),
//                 },
//             ]
//             .into_boxed_slice()
//         );
//     }

//     #[test]
//     fn test_syntax_rule_parse() {
//         let mut vm = VirtualMachine::default();
//         let mut rules = SyntaxRules::new(
//             vm.interner().get_or_intern_static("rev-apply"),
//             Default::default(),
//         );

//         rules
//             .parse(
//                 &mut vm,
//                 &parse_expr("( rev-apply fun arg ... )"),
//                 &parse_expr("( apply fun (reverse arg ...) )"),
//             )
//             .unwrap();

//         assert_eq!(
//             rules.rules[0].0,
//             ListPattern {
//                 patterns: vec![
//                     Pattern::Literal(vm.interner().get_or_intern_static("rev-apply").into()),
//                     Pattern::Capture("fun".into()),
//                     Pattern::Repeat(Box::new(Pattern::Capture("arg".into()))),
//                 ]
//                 .into_boxed_slice()
//             }
//         );

//         assert_eq!(
//             rules.rules[0].1,
//             ListTemplate {
//                 template: vec![
//                     Template::Literal(SourceNode::synth_atom(AtomKind::Symbol, "apply")),
//                     Template::Replace("fun".into()),
//                     Template::List(ListTemplate {
//                         template: vec![
//                             Template::Literal(SourceNode::synth_atom(AtomKind::Symbol, "reverse")),
//                             Template::Repeat(Box::new(Template::Replace("arg".into()))),
//                         ]
//                         .into_boxed_slice()
//                     })
//                 ]
//                 .into_boxed_slice()
//             }
//         );
//     }

//     #[test]
//     fn test_pattern_matches_nested() {
//         let mut vm = VirtualMachine::default();

//         let pattern = list_pattern![
//             Pattern::Ignored,
//             list_pattern![list_pattern![
//                 Pattern::Capture("foo".into()),
//                 Pattern::Literal(Value::from(3.15)),
//             ],],
//             list_pattern![
//                 Pattern::Literal(vm.interner().get_or_intern_static("add").into()),
//                 Pattern::Literal(Value::from(1)),
//                 Pattern::Capture("bar".into()),
//             ],
//         ];

//         let mut res = pattern
//             .matches(&mut vm, &parse_list("(lol ((\"hello\" 3.15)) (add 1 foo))"))
//             .unwrap();

//         assert_eq!(
//             res.get_single(&"foo").unwrap(),
//             SourceNode::Atom {
//                 kind: AtomKind::String,
//                 atom: "hello".into(),
//                 pos: 8.into(),
//             }
//         );

//         assert_eq!(
//             res.get_single(&"bar").unwrap(),
//             SourceNode::Atom {
//                 kind: AtomKind::Symbol,
//                 atom: "foo".into(),
//                 pos: 29.into(),
//             }
//         );
//     }

//     // #[test]
//     // fn test_pattern_matches_simple_repeated() {
//     //     let mut interner = Compiler::default();

//     //     let pat = pattern!(int => (1 ...));
//     //     let res = pat.matches(list_pattern![1, 1, 1].unwrap_pair().unwrap().as_ref());

//     //     assert!(res.is_some());

//     //     let pat = pattern!(int => ({qux} ...));
//     //     let res = pat.matches(list_pattern![1, 2, 3].unwrap_pair().unwrap().as_ref());

//     //     let res = res.unwrap();
//     //     assert_eq!(
//     //         res.get(&int.intern("qux")).unwrap(),
//     //         Bound::Repeating(vec![
//     //             Bound::Single(int.number("1")),
//     //             Bound::Single(int.number("2")),
//     //             Bound::Single(int.number("3"))
//     //         ])
//     //     );
//     // }

//     //     #[test]
//     //     fn test_pattern_matches_nested_repeated() {
//     //         let mut int = Interner::default();

//     //         let pat = pattern!(int => (let (({var} {val}) ...) {body}));

//     //         let body = list_pattern![int.symbol("+"), int.symbol("π"), int.symbol("τ"),];

//     //         let res = pat.matches(
//     //             list_pattern![
//     //                 int.symbol("let"),
//     //                 list_pattern![
//     //                     list_pattern![int.symbol("π"), 3.1416,],
//     //                     list_pattern![int.symbol("τ"), 6.2832,],
//     //                 ],
//     //                 body.clone(),
//     //             ]
//     //             .unwrap_pair()
//     //             .unwrap()
//     //             .as_ref(),
//     //         );

//     //         let res = res.unwrap();

//     //         assert_eq!(
//     //             res.get(&int.intern("var")).unwrap(),
//     //             Bound::Repeating(vec![
//     //                 Bound::Single(int.symbol("π")),
//     //                 Bound::Single(int.symbol("τ")),
//     //             ])
//     //         );

//     //         assert_eq!(
//     //             res.get(&int.intern("val")).unwrap(),
//     //             Bound::Repeating(vec![
//     //                 Bound::Single(int.number("3.1416")),
//     //                 Bound::Single(int.number("6.2832")),
//     //             ])
//     //         );

//     //         assert_eq!(res.get(&int.intern("body")).unwrap(), Bound::Single(body));
//     //     }
// }
