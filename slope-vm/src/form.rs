use slope_parse::SourceNode;

use crate::{
    compile::SyntaxResult,
    syntax::{Match, Pattern},
    vm::AllocationContext,
};

pub(crate) fn match_unary(
    ctx: &mut AllocationContext<'_>,
    list: &[SourceNode],
    name: impl AsRef<str>,
) -> SyntaxResult<SourceNode> {
    let pattern = list_pattern![Pattern::Ignored, Pattern::Capture(name.as_ref().into()),];
    let mut matches = pattern.matches(ctx, list)?;
    Ok(matches.get_single(name).unwrap())
}

pub(crate) fn match_binary(
    ctx: &mut AllocationContext<'_>,
    list: &[SourceNode],
    name0: impl AsRef<str>,
    name1: impl AsRef<str>,
) -> SyntaxResult<(SourceNode, SourceNode)> {
    let pattern = list_pattern![
        Pattern::Ignored,
        Pattern::Capture(name0.as_ref().into()),
        Pattern::Capture(name1.as_ref().into()),
    ];

    let mut matches = pattern.matches(ctx, list)?;

    Ok((
        matches.get_single(name0).unwrap(),
        matches.get_single(name1).unwrap(),
    ))
}

pub(crate) fn match_ternary(
    ctx: &mut AllocationContext<'_>,
    list: &[SourceNode],
    name0: impl AsRef<str>,
    name1: impl AsRef<str>,
    name2: impl AsRef<str>,
) -> SyntaxResult<(SourceNode, SourceNode, SourceNode)> {
    let pattern = list_pattern![
        Pattern::Literal(
            ctx.interner()
                .intern(list[0].as_symbol().unwrap().as_str())
                .into()
        ),
        Pattern::Capture(name0.as_ref().into()),
        Pattern::Capture(name1.as_ref().into()),
        Pattern::Capture(name2.as_ref().into()),
    ];

    let mut matches = pattern.matches(ctx, list)?;

    Ok((
        matches.get_single(name0).unwrap(),
        matches.get_single(name1).unwrap(),
        matches.get_single(name2).unwrap(),
    ))
}

pub(crate) fn match_variadic(
    ctx: &mut AllocationContext<'_>,
    list: &[SourceNode],
    arg: impl AsRef<str>,
) -> SyntaxResult<Box<[SourceNode]>> {
    let pattern = list_pattern![
        Pattern::Literal(
            ctx.interner()
                .intern(list[0].as_symbol().unwrap().as_str())
                .into()
        ),
        repeat_pattern!(Pattern::Capture(arg.as_ref().into())),
    ];

    let mut matches = pattern.matches(ctx, list)?;

    Ok(matches
        .get_repeating(arg)
        .unwrap()
        .filter_map(Match::into_single)
        .collect())
}

// 4.1.5. Conditionals
#[derive(Debug)]
pub(crate) struct IfMatch {
    pub(crate) test: SourceNode,
    pub(crate) consequent: SourceNode,
    pub(crate) alternate: Option<SourceNode>,
}

pub(crate) fn match_if(
    ctx: &mut AllocationContext<'_>,
    list: &[SourceNode],
) -> SyntaxResult<IfMatch> {
    match match_ternary(ctx, list, "test", "consequent", "alternate") {
        Ok((test, consequent, alternate)) => Ok(IfMatch {
            test,
            consequent,
            alternate: Some(alternate),
        }),

        Err(err) => {
            // Try without alternate
            if let Ok((test, consequent)) = match_binary(ctx, list, "test", "consequent") {
                Ok(IfMatch {
                    test,
                    consequent,
                    alternate: None,
                })
            } else {
                Err(err)
            }
        }
    }
}

#[derive(Debug)]
pub(crate) struct FnMatch {
    pub(crate) params: Vec<SourceNode>, // TODO use Box<[]>?
    pub(crate) body: Vec<SourceNode>,
}

pub(crate) fn match_fn(
    ctx: &mut AllocationContext<'_>,
    list: &[SourceNode],
) -> SyntaxResult<FnMatch> {
    let pattern = list_pattern![
        Pattern::Literal(ctx.interner().intern_static("fn").into()),
        list_pattern![repeat_pattern!(Pattern::Capture("param".into())),],
        repeat_pattern!(Pattern::Capture("body".into())),
    ];

    let mut matches = pattern.matches(ctx, list)?;
    let params = matches.get_repeating("param").unwrap();
    let body = matches.get_repeating("body").unwrap();

    let params = params.filter_map(Match::into_single).collect();
    let body = body.filter_map(Match::into_single).collect();
    Ok(FnMatch { params, body })
}

#[derive(Debug)]
pub(crate) struct LetMatch {
    pub(crate) bindings: Vec<(SourceNode, SourceNode)>,
    pub(crate) body: Vec<SourceNode>,
}

// TODO: No source node cloning.
pub(crate) fn match_let(
    ctx: &mut AllocationContext<'_>,
    list: &[SourceNode],
) -> SyntaxResult<LetMatch> {
    let pattern = list_pattern![
        Pattern::Literal(ctx.interner().intern_static("let").into()),
        list_pattern![repeat_pattern!(list_pattern![
            Pattern::Capture("variable".into()),
            Pattern::Capture("init".into()),
        ]),],
        repeat_pattern!(Pattern::Capture("body".into())),
    ];

    let mut matches = pattern.matches(ctx, list)?;
    let variables = matches.get_repeating("variable").unwrap();
    let inits = matches.get_repeating("init").unwrap();
    let body = matches.get_repeating("body").unwrap();

    let mut bindings = Vec::with_capacity(variables.size_hint().0);
    for (variable, init) in variables.zip(inits) {
        bindings.push((variable.into_single().unwrap(), init.into_single().unwrap()));
    }

    let body = body.filter_map(Match::into_single).collect();
    Ok(LetMatch { bindings, body })
}

#[derive(Debug)]
pub(crate) struct DefMatch {
    pub(crate) variable: SourceNode,
    pub(crate) init: SourceNode,
}

pub(crate) fn match_def(
    ctx: &mut AllocationContext<'_>,
    list: &[SourceNode],
) -> SyntaxResult<DefMatch> {
    let pattern = list_pattern![
        Pattern::Literal(ctx.interner().intern_static("def").into()),
        Pattern::Capture("variable".into()),
        Pattern::Capture("init".into()),
    ];

    let mut matches = pattern.matches(ctx, list)?;
    let variable = matches.get_single("variable").unwrap();
    let init = matches.get_single("init").unwrap();

    Ok(DefMatch { variable, init })
}

#[derive(Default, Debug)]
pub(crate) struct SyntaxRulesMatch {
    pub(crate) literals: Vec<SourceNode>,
    pub(crate) rules: Vec<(SourceNode, SourceNode)>,
}

#[derive(Default, Debug)]
pub(crate) struct LetSyntaxMatch {
    pub(crate) bindings: Vec<(SourceNode, SyntaxRulesMatch)>,
    pub(crate) body: Vec<SourceNode>,
}

pub(crate) fn match_let_syntax(
    ctx: &mut AllocationContext<'_>,
    list: &[SourceNode],
) -> SyntaxResult<LetSyntaxMatch> {
    let pattern = list_pattern![
        Pattern::Literal(ctx.interner().intern_static("let-syntax").into()),
        list_pattern![repeat_pattern!(list_pattern![
            Pattern::Capture("keyword".into()),
            list_pattern![
                Pattern::Literal(ctx.interner().intern_static("syntax-rules").into()),
                list_pattern![repeat_pattern!(Pattern::Capture("literal".into())),],
                repeat_pattern!(list_pattern![
                    Pattern::Capture("pattern".into()),
                    Pattern::Capture("template".into()),
                ]),
            ],
        ]),],
        repeat_pattern!(Pattern::Capture("body".into())),
    ];

    let mut matches = pattern.matches(ctx, list)?;
    let keywords = matches.get_repeating("keyword").unwrap();
    let mut literals = matches.get_repeating("literal").unwrap();
    let patterns = matches.get_repeating("pattern").unwrap();
    let templates = matches.get_repeating("template").unwrap();
    let body = matches.get_repeating("body").unwrap();

    let mut bindings = Vec::with_capacity(keywords.size_hint().0);
    for (keyword, (patterns, templates)) in keywords.zip(patterns.zip(templates)) {
        let mut rules = SyntaxRulesMatch::default();

        if let Some(literals) = literals.next() {
            rules.literals = literals
                .into_repeating()
                .unwrap()
                .filter_map(Match::into_single)
                .collect();
        }

        for (pattern, template) in patterns
            .into_repeating()
            .unwrap()
            .zip(templates.into_repeating().unwrap())
        {
            rules.rules.push((
                pattern.into_single().unwrap(),
                template.into_single().unwrap(),
            ));
        }

        bindings.push((keyword.into_single().unwrap(), rules));
    }

    let body = body.filter_map(Match::into_single).collect();
    Ok(LetSyntaxMatch { bindings, body })
}

#[derive(Default, Debug)]
pub(crate) struct DefSyntaxMatch {
    pub(crate) keyword: SourceNode,
    pub(crate) syntax: SyntaxRulesMatch,
}

pub(crate) fn match_def_syntax(
    ctx: &mut AllocationContext<'_>,
    list: &[SourceNode],
) -> SyntaxResult<DefSyntaxMatch> {
    let pattern = list_pattern![
        Pattern::Literal(ctx.interner().intern_static("def-syntax").into()),
        Pattern::Capture("keyword".into()),
        list_pattern![
            Pattern::Literal(ctx.interner().intern_static("syntax-rules").into()),
            list_pattern![repeat_pattern!(Pattern::Capture("literal".into())),],
            repeat_pattern!(list_pattern![
                Pattern::Capture("pattern".into()),
                Pattern::Capture("template".into()),
            ]),
        ],
    ];

    let mut matches = pattern.matches(ctx, list)?;
    let keyword = matches.get_single("keyword").unwrap();
    let literals = matches.get_repeating("literal").unwrap();
    let patterns = matches.get_repeating("pattern").unwrap();
    let templates = matches.get_repeating("template").unwrap();

    let mut syntax = SyntaxRulesMatch::default();

    syntax.literals = literals.filter_map(Match::into_single).collect();

    for (pattern, template) in patterns.zip(templates) {
        syntax.rules.push((
            pattern.into_single().unwrap(),
            template.into_single().unwrap(),
        ));
    }

    Ok(DefSyntaxMatch { keyword, syntax })
}

#[derive(Default, Debug)]
pub(crate) struct ExportMatch {
    pub(crate) identifiers: Box<[SourceNode]>,
}

pub(crate) fn match_export(
    ctx: &mut AllocationContext<'_>,
    list: &[SourceNode],
) -> SyntaxResult<ExportMatch> {
    let pattern = list_pattern![
        Pattern::Literal(ctx.interner().intern_static("export").into()),
        repeat_pattern!(Pattern::Capture("identifier".into())),
    ];

    let mut matches = pattern.matches(ctx, list)?;
    let identifiers = matches.get_repeating("identifier").unwrap();

    let identifiers = identifiers.filter_map(Match::into_single).collect();
    Ok(ExportMatch { identifiers })
}

#[derive(Default, Debug)]
pub(crate) struct ImportMatch {
    pub(crate) path: SourceNode,
}

pub(crate) fn match_import(
    ctx: &mut AllocationContext<'_>,
    list: &[SourceNode],
) -> SyntaxResult<ImportMatch> {
    let pattern = list_pattern![
        Pattern::Literal(ctx.interner().intern_static("import").into()),
        Pattern::Capture("path".into()),
    ];

    let mut matches = pattern.matches(ctx, list)?;
    let path = matches.get_single("path").unwrap();
    Ok(ImportMatch { path })
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use slope_parse::{parse, AtomKind};

//     fn parse_list(input: &str) -> Box<[SourceNode]> {
//         match parse(input).next().unwrap().unwrap() {
//             SourceNode::List { inner, .. } => inner,
//             _ => panic!("not a list"),
//         }
//     }

//     #[test]
//     fn test_unary_pattern() {
//         let mut vm = VirtualMachine::default();
//         let mut ctx = vm.mutate();
//         let res = match_unary(&mut ctx, &parse_list("(lol 3.14)"), "var");

//         assert_eq!(
//             res.unwrap(),
//             SourceNode::Atom {
//                 kind: AtomKind::Number,
//                 atom: "3.14".into(),
//                 pos: 5.into(),
//             }
//         );
//     }

//     #[test]
//     fn test_unary_pattern_error() {
//         let mut vm = VirtualMachine::default();
//         let mut ctx = vm.mutate();
//         let res = match_unary(&mut ctx, &parse_list("(lol 3.14 6.28)"), "var");

//         assert!(res.is_err());
//     }

//     #[test]
//     fn test_binary_pattern() {
//         let mut vm = VirtualMachine::default();
//         let mut ctx = vm.mutate();
//         let res = match_binary(&mut ctx, &parse_list("(lol 3.14 6.28)"), "var1", "var2");

//         assert_eq!(
//             res.unwrap().1,
//             SourceNode::Atom {
//                 kind: AtomKind::Number,
//                 atom: "6.28".into(),
//                 pos: 10.into(),
//             }
//         );
//     }

//     #[test]
//     fn test_binary_pattern_error() {
//         let mut vm = VirtualMachine::default();
//         let mut ctx = vm.mutate();
//         let res = match_binary(&mut ctx, &parse_list("(lol 3.14)"), "var1", "var2");

//         assert!(res.is_err());
//     }

//     #[test]
//     fn test_let_pattern() {
//         let mut vm = VirtualMachine::default();
//         let mut ctx = vm.mutate();
//         let res = match_let(
//             &mut ctx,
//             &parse_list("(let ((a 2) (b (+ 3 5))) (set a 8) (+ a b))"),
//         );

//         assert_eq!(
//             res.unwrap().bindings[0],
//             (
//                 SourceNode::Atom {
//                     kind: AtomKind::Symbol,
//                     atom: "a".into(),
//                     pos: 7.into(),
//                 },
//                 SourceNode::Atom {
//                     kind: AtomKind::Number,
//                     atom: "2".into(),
//                     pos: 9.into(),
//                 },
//             )
//         );
//     }

//     // #[test]
//     // fn test_let_syntax_pattern() {
//     //     let res = match_let_syntax(&mut Default::default(), &parse_list(
//     //         "(let-syntax \n\
//     //         ((unless \n\
//     //           (syntax-rules (unused) \n\
//     //             ((unless test then) (if test nil then)) \n\
//     //             ((unless test then else) (if test else then)) \n\
//     //           ))) \n\
//     //         (unless (= 1 2) 'yes 'no))",
//     //     ))
//     //     .unwrap();

//     //     assert_eq!(
//     //         res.bindings[0].0,
//     //         SourceNode {
//     //             value: SourceNode::Symbol("unless".into()),
//     //             range: Location { line: 2, col: 3 }..Location { line: 2, col: 9 },
//     //         }
//     //     );

//     //     assert_eq!(
//     //         res.bindings[0].1.literals,
//     //         vec![SourceNode {
//     //             value: SourceNode::Symbol("unused".into()),
//     //             range: Location { line: 3, col: 16 }..Location { line: 3, col: 22 },
//     //         }]
//     //     );

//     //     assert_eq!(
//     //         res.bindings[0].1.rules[0],
//     //         (
//     //             SourceNode {
//     //                 value: SourceNode::ProperList(
//     //                     vec![
//     //                         SourceNode {
//     //                             value: SourceNode::Symbol("unless".into()),
//     //                             range: Location { line: 4, col: 3 }..Location { line: 4, col: 9 },
//     //                         },
//     //                         SourceNode {
//     //                             value: SourceNode::Symbol("test".into()),
//     //                             range: Location { line: 4, col: 10 }..Location { line: 4, col: 14 },
//     //                         },
//     //                         SourceNode {
//     //                             value: SourceNode::Symbol("then".into()),
//     //                             range: Location { line: 4, col: 15 }..Location { line: 4, col: 19 },
//     //                         },
//     //                     ]
//     //                     .into_boxed_slice()
//     //                 ),
//     //                 range: Location { line: 4, col: 2 }..Location { line: 4, col: 20 },
//     //             },
//     //             SourceNode {
//     //                 value: SourceNode::ProperList(
//     //                     vec![
//     //                         SourceNode {
//     //                             value: SourceNode::Symbol("if".into()),
//     //                             range: Location { line: 4, col: 22 }..Location { line: 4, col: 24 },
//     //                         },
//     //                         SourceNode {
//     //                             value: SourceNode::Symbol("test".into()),
//     //                             range: Location { line: 4, col: 25 }..Location { line: 4, col: 29 },
//     //                         },
//     //                         SourceNode {
//     //                             value: SourceNode::Symbol("nil".into()),
//     //                             range: Location { line: 4, col: 30 }..Location { line: 4, col: 33 },
//     //                         },
//     //                         SourceNode {
//     //                             value: SourceNode::Symbol("then".into()),
//     //                             range: Location { line: 4, col: 34 }..Location { line: 4, col: 38 },
//     //                         },
//     //                     ]
//     //                     .into_boxed_slice()
//     //                 ),
//     //                 range: Location { line: 4, col: 21 }..Location { line: 4, col: 39 },
//     //             }
//     //         )
//     //     );
//     // }
// }
