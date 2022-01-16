mod source;

use std::{
    borrow::Borrow,
    fmt::{self, Debug, Display, Formatter},
    ops::Deref,
    path::PathBuf,
};

use nom_locate::LocatedSpan;
use smol_str::SmolStr;
use unicode_categories::UnicodeCategories;

use nom::{
    branch::alt,
    bytes::complete::{escaped, tag},
    character::complete::{char, line_ending, multispace1, none_of, not_line_ending, one_of},
    combinator::{map, opt, recognize},
    error::{ErrorKind as NomKind, ParseError as NomError},
    multi::{many0, many1},
    number::complete::recognize_float,
    sequence::{pair, tuple},
    AsChar, Err, IResult, InputLength, InputTakeAtPosition,
};

use source::BytePos;
pub use source::ByteRange;

#[cfg(not(debug_assertions))]
mod limit {
    pub(super) const MAX_LENGTH: u32 = u32::MAX;
    pub(super) const MAX_DEPTH: u32 = 1 << 10;
}

#[cfg(debug_assertions)]
mod limit {
    pub(super) const MAX_LENGTH: u32 = 1 << 24;
    pub(super) const MAX_DEPTH: u32 = 1 << 8;
}

#[derive(Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Atom(SmolStr);

impl Atom {
    #[inline]
    pub fn new(text: impl AsRef<str>) -> Self {
        Self(SmolStr::new(text))
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl Debug for Atom {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.0, fmt)
    }
}

impl Display for Atom {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, fmt)
    }
}

impl Borrow<str> for Atom {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl Deref for Atom {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl From<&str> for Atom {
    #[inline]
    fn from(text: &str) -> Self {
        Self(text.into())
    }
}

impl PartialEq<str> for Atom {
    fn eq(&self, other: &str) -> bool {
        self.0 == other
    }
}

impl<'a> PartialEq<&'a str> for Atom {
    fn eq(&self, other: &&'a str) -> bool {
        self.0 == *other
    }
}

impl PartialEq<String> for Atom {
    fn eq(&self, other: &String) -> bool {
        self.0 == other
    }
}

impl<'a> PartialEq<&'a String> for Atom {
    fn eq(&self, other: &&'a String) -> bool {
        self.0 == *other
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum FileName {
    Real(PathBuf),
    Fictional(&'static str),
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct SrcFile {
    name: FileName,
    lines: Vec<BytePos>,
}

impl Display for FileName {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            FileName::Real(path) => write!(fmt, "{}", path.display()),
            FileName::Fictional(name) => write!(fmt, "<{}>", name),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
#[repr(u8)]
pub enum AtomKind {
    // Value types
    // Char,
    Bool,
    Symbol,
    Number,
    String,

    // Trivia
    Comment,
    Whitespace,
}

// TODO Use compression by reusing identical nodes. What to do with position
// information derived from the span pointers into the source though?
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum SourceNode {
    // Leaf nodes point to source span.
    Atom {
        kind: AtomKind,
        atom: Atom,
        pos: BytePos,
    },

    // Non-leaf nodes point to child nodes.
    List {
        inner: Box<[SourceNode]>,
        range: ByteRange,
    },

    Cons {
        inner: Box<[SourceNode]>,
        range: ByteRange,
    },

    Quoted {
        inner: Box<SourceNode>,
        range: ByteRange,
    },
}

impl Default for SourceNode {
    fn default() -> Self {
        Self::List {
            inner: Box::new([]),
            range: Default::default(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(dead_code)]
enum ParseErrorKind {
    Incomplete,
    InvalidExpression,
    ExpectedSpace,
    ExpectedChar(char),
    MaximumExpressionDepth,
    InputTooLarge,
    Other,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    kind: ParseErrorKind,
    origin: ByteRange,
}

impl ParseError {
    pub fn is_incomplete(&self) -> bool {
        self.kind == ParseErrorKind::Incomplete
    }

    pub fn origin(&self) -> ByteRange {
        self.origin
    }
}

impl Display for ParseError {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        write!(fmt, "{}", self.kind)
    }
}

impl Display for ParseErrorKind {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            ParseErrorKind::Incomplete => write!(fmt, "unexpected end of input"),
            ParseErrorKind::InvalidExpression => write!(fmt, "invalid expression"),
            ParseErrorKind::ExpectedSpace => write!(fmt, "expected space"),
            ParseErrorKind::ExpectedChar(what) => write!(fmt, "expected '{}'", what),
            ParseErrorKind::MaximumExpressionDepth => {
                write!(fmt, "maximum expression depth reached")
            }
            ParseErrorKind::InputTooLarge => write!(
                fmt,
                "input too large; maximum is {}MB",
                limit::MAX_LENGTH / 1024 / 1024
            ),
            ParseErrorKind::Other => write!(fmt, "unable to parse"),
        }
    }
}

trait Lower: Fn(Box<[SourceNode]>) -> Box<[SourceNode]> {}
impl<T> Lower for T where T: Fn(Box<[SourceNode]>) -> Box<[SourceNode]> {}

#[derive(Debug)]
struct Parser<'s, L> {
    span: Span<'s>,
    parsed: <Vec<SourceNode> as IntoIterator>::IntoIter,
    lower: L,
}

impl<'s, L> Parser<'s, L> {
    fn fuse(&mut self) {
        self.span = Span::new(Default::default());
    }
}

type ParseResult = Result<SourceNode, ParseError>;

pub fn parse_lossless<'s>(span: &'s str) -> impl Iterator<Item = ParseResult> + 's {
    Parser {
        span: Span::new(span),
        parsed: vec![].into_iter(),
        lower: |list| list, // No filtering, node list identity.
    }
}

pub fn parse<'s>(span: &'s str) -> impl Iterator<Item = ParseResult> + 's {
    Parser {
        span: Span::new(span),
        parsed: vec![].into_iter(),
        lower: lower_tree, // Remove whitespace, flatten cons expressions.
    }
}

impl<'s, L: Lower> Iterator for Parser<'s, L> {
    type Item = ParseResult;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(next) = self.parsed.next() {
            Some(Ok(next))
        } else {
            if self.span.input_len() > limit::MAX_LENGTH as usize {
                self.fuse();
                return Some(Err(ParseError {
                    kind: ParseErrorKind::InputTooLarge,
                    origin: Default::default(),
                }));
            }

            match parse_next(self.span) {
                Ok((input, nodes)) => {
                    self.span = input;
                    let mut nodes = Vec::from((self.lower)(nodes)).into_iter();
                    if let Some(node) = nodes.next() {
                        self.parsed = nodes;
                        Some(Ok(node))
                    } else {
                        None
                    }
                }

                Err(Err::Incomplete(..)) => {
                    self.fuse();
                    Some(Err(ParseError {
                        kind: ParseErrorKind::Incomplete,
                        origin: (self.span.location_offset()..self.span.location_offset() + 1)
                            .into(),
                    }))
                }

                Err(Err::Failure(err)) | Err(Err::Error(err)) => {
                    self.fuse();
                    Some(Err(err))
                }
            }
        }
    }
}

const TRUE: &str = &"#t";
const FALSE: &str = &"#f";

type Span<'s> = LocatedSpan<&'s str>;
type InternalResult<'s, T = SourceNode> = IResult<Span<'s>, T, ParseError>;

impl<'s> NomError<Span<'s>> for ParseError {
    fn from_error_kind(input: Span<'s>, _kind: NomKind) -> Self {
        let kind = if input.input_len() == 0 {
            ParseErrorKind::Incomplete
        } else {
            ParseErrorKind::Other
        };

        // todo!()
        ParseError {
            kind,
            origin: Default::default(),
        }
    }

    fn append(input: Span<'s>, kind: NomKind, _other: Self) -> Self {
        Self::from_error_kind(input, kind)
    }

    fn from_char(input: Span<'s>, char: char) -> Self {
        let kind = if input.input_len() == 0 {
            ParseErrorKind::Incomplete
        } else {
            ParseErrorKind::ExpectedChar(char)
        };

        // todo!()
        ParseError {
            kind,
            origin: Default::default(),
        }
    }
}

// fn error_type(what: ErrorKind) -> impl FnOnce(Err<InternalErr>) -> Err<InternalErr> {
//     move |err: Err<InternalErr>| {
//         err.map(|err| {
//             if err.reason == ErrorKind::Incomplete {
//                 err
//             } else {
//                 InternalErr {
//                     reason: what,
//                     ..err
//                 }
//             }
//         })
//     }
// }

fn symbol_init1<'s>(input: Span<'s>) -> InternalResult<'s, Span<'s>> {
    // Based on R7RS:
    // it is an error for the first character to have a general category of Nd, Mc, or Me
    // http://www.unicode.org/Public/UNIDATA/UnicodeData.txt
    input.split_at_position1_complete(
        |c| {
            !c.as_char().is_letter()
                && !c.as_char().is_number_letter()
                && !c.as_char().is_number_other()
                && !c.as_char().is_mark_nonspacing()
                && !c.as_char().is_symbol()
                && !c.as_char().is_punctuation_dash()
                && !c.as_char().is_punctuation_connector()
                && !c.as_char().is_punctuation_other()
                || c == ';'
                || c == '\'' // reserved
        },
        NomKind::Alpha,
    )
}

fn symbol_rest0<'s>(input: Span<'s>) -> InternalResult<'s, Span<'s>> {
    // Based on R7RS:
    // Lu, Ll, Lt, Lm, Lo, Mn, Mc, Me, Nd, Nl, No, Pd, Pc, Po, Sc, Sm, Sk, So, or Co
    // http://www.unicode.org/Public/UNIDATA/UnicodeData.txt
    input.split_at_position_complete(|c| {
        !c.as_char().is_letter()
            && !c.as_char().is_number()
            && !c.as_char().is_mark()
            && !c.as_char().is_symbol()
            && !c.as_char().is_punctuation_dash()
            && !c.as_char().is_punctuation_connector()
            && !c.as_char().is_punctuation_other()
            || c == ';'
            || c == '\'' // reserved
    })
}

fn line_ending_or_eof<'s>(input: Span<'s>) -> InternalResult<'s, Span<'s>> {
    if input.input_len() == 0 {
        Ok((input, input))
    } else {
        line_ending(input)
    }
}

fn whitespace<'s>(input: Span<'s>) -> InternalResult<'s> {
    map(multispace1, SourceNode::span_of_kind(AtomKind::Whitespace))(input)
}

fn comment<'s>(input: Span<'s>) -> InternalResult<'s> {
    map(
        recognize(tuple((char(';'), not_line_ending, line_ending_or_eof))),
        SourceNode::span_of_kind(AtomKind::Comment),
    )(input)
}

fn sep0<'s>(input: Span<'s>) -> InternalResult<'s, Vec<SourceNode>> {
    many0(alt((whitespace, comment)))(input)
}

fn sep1<'s>(input: Span<'s>) -> InternalResult<'s, Vec<SourceNode>> {
    many1(alt((whitespace, comment)))(input)
}

fn left_paren<'s>(input: Span<'s>) -> InternalResult<'s, ()> {
    map(tag("("), |_| ())(input)
}

fn left_paren_sep0<'s>(input: Span<'s>) -> InternalResult<'s, Vec<SourceNode>> {
    let (input, _) = left_paren(input)?;
    let (input, seps) = sep0(input)?;
    Ok((input, seps))
}

fn right_paren<'s>(input: Span<'s>) -> InternalResult<'s, ()> {
    map(tag(")"), |_| ())(input)
}

fn right_sep0_paren<'s>(input: Span<'s>) -> InternalResult<'s, Vec<SourceNode>> {
    let (input, seps) = sep0(input)?;
    let (input, _) = right_paren(input)?;
    Ok((input, seps))
}

fn cons_dot<'s>(input: Span<'s>) -> InternalResult<'s, ()> {
    map(tag("."), |_| ())(input)
}

fn cons_sep1_dot_sep1<'s>(
    input: Span<'s>,
) -> InternalResult<'s, (Vec<SourceNode>, Vec<SourceNode>)> {
    let (input, (trailing, _, leading)) = tuple((sep1, cons_dot, sep1))(input)?;

    Ok((input, (trailing, leading)))
}

fn double_quote<'s>(input: Span<'s>) -> InternalResult<'s, ()> {
    map(tag("\""), |_| ())(input)
}

fn parse_bool<'s>(input: Span<'s>) -> InternalResult<'s> {
    map(
        alt((tag(TRUE), tag(FALSE))),
        SourceNode::span_of_kind(AtomKind::Bool),
    )(input)
}

fn parse_symbol<'s>(input: Span<'s>) -> InternalResult<'s> {
    map(
        recognize(pair(symbol_init1, symbol_rest0)),
        SourceNode::span_of_kind(AtomKind::Symbol),
    )(input)
}

fn parse_number<'s>(input: Span<'s>) -> InternalResult<'s> {
    map(recognize_float, SourceNode::span_of_kind(AtomKind::Number))(input)
}

fn parse_string<'s>(input: Span<'s>) -> InternalResult<'s> {
    let (input, _) = double_quote(input)?;

    let (input, string) = opt(map(
        escaped(none_of("\"\\"), '\\', one_of("\"\\nrt")),
        SourceNode::span_of_kind(AtomKind::String),
    ))(input)?;

    let string = string.unwrap_or_else(|| SourceNode::Atom {
        kind: AtomKind::String,
        atom: Atom::new(""),
        pos: input.location_offset().into(),
    });

    let (input, _) = double_quote(input)?;

    Ok((input, string))
}

fn parse_quoted<'s>(depth: u32) -> impl Fn(Span<'s>) -> InternalResult<'s> {
    move |input| {
        map(tuple((tag("'"), parse_expression(depth))), |(_, inner)| {
            SourceNode::Quoted {
                inner: Box::new(inner),
                range: Default::default(),
            }
        })(input)
    }
}

fn parse_list<'s>(depth: u32) -> impl Fn(Span<'s>) -> InternalResult<'s> {
    move |input| {
        let lo = input.location_offset().into();
        let (input, leading) = left_paren_sep0(input)?;
        let mut inner = leading;

        if let (input, Some(trailing)) = opt(right_sep0_paren)(input)? {
            let hi = input.location_offset().into();
            inner.extend(trailing);

            return Ok((
                input,
                SourceNode::List {
                    inner: inner.into_boxed_slice(),
                    range: ByteRange { lo, hi },
                },
            ));
        }

        let (input, expr) = parse_expression(depth)(input)?;
        inner.push(expr);

        let mut loop_input = input;

        loop {
            let input = loop_input;

            if let (input, Some(trailing)) = opt(right_sep0_paren)(input)? {
                inner.extend(trailing);

                return Ok((
                    input,
                    SourceNode::List {
                        inner: inner.into_boxed_slice(),
                        range: ByteRange {
                            lo,
                            hi: input.location_offset().into(),
                        },
                    },
                ));
            }

            if let (input, Some((trailing, mut cons))) = opt(cons_sep1_dot_sep1)(input)? {
                inner.extend(trailing);

                let (input, expr) = parse_expression(depth)(input)?;
                let (input, trailing) = right_sep0_paren(input)?;

                let hi = input.location_offset().into();
                cons.push(expr);
                cons.extend(trailing);

                let cons_lo = cons.first().map(SourceNode::range).unwrap_or_default().lo - 1;
                let cons_hi = cons.last().map(SourceNode::range).unwrap_or_default().hi;

                inner.push(SourceNode::Cons {
                    inner: cons.into_boxed_slice(),
                    range: ByteRange {
                        lo: cons_lo,
                        hi: cons_hi,
                    },
                });

                return Ok((
                    input,
                    SourceNode::List {
                        inner: inner.into_boxed_slice(),
                        range: ByteRange { lo, hi },
                    },
                ));
            }

            let (input, seps) = sep1(input)?; //.map_err(error_type(ErrorKind::ExpectedSpace))?;
            inner.extend(seps);

            let (input, expr) = parse_expression(depth)(input)?;
            inner.push(expr);

            loop_input = input;
        }
    }
}

fn parse_expression<'s>(depth: u32) -> impl Fn(Span<'s>) -> InternalResult<'s> {
    move |input| {
        if depth >= limit::MAX_DEPTH {
            return Err(Err::Failure(ParseError {
                kind: ParseErrorKind::MaximumExpressionDepth,
                origin: Default::default(),
            }));
        }

        alt((
            parse_bool,
            parse_string,
            parse_number,
            parse_symbol,
            parse_quoted(depth + 1),
            parse_list(depth + 1),
        ))(input)
    }
    // .map_err(error_type(ErrorKind::InvalidExpression))
}

fn parse_next<'s>(input: Span<'s>) -> InternalResult<'s, Box<[SourceNode]>> {
    let (input, mut leading) = map(opt(sep1), Option::unwrap_or_default)(input)?;

    if input.input_len() == 0 {
        return Ok((input, leading.into_boxed_slice()));
    }

    let (input, expr) = parse_expression(0)(input)?;
    leading.push(expr);

    if input.input_len() != 0 {
        let (input, trailing) = sep1(input)?; //.map_err(error_type(ErrorKind::ExpectedSpace))?;
        leading.extend(trailing);
        Ok((input, leading.into_boxed_slice()))
    } else {
        Ok((input, leading.into_boxed_slice()))
    }
}

fn lower_tree(mut list: Box<[SourceNode]>) -> Box<[SourceNode]> {
    let mut new = vec![];

    'inner: loop {
        for item in Vec::from(list).into_iter() {
            if item.is_trivia() {
                continue;
            }

            // Lower trailing cons expressions.
            match item {
                SourceNode::Cons { inner, .. } => {
                    for item in Vec::from(inner).into_iter() {
                        if let SourceNode::List { inner, .. } = item {
                            list = inner;
                            continue 'inner;
                        } else if !item.is_trivia() {
                            new.push(SourceNode::Cons {
                                inner: Box::new([item]),
                                range: Default::default(),
                            });

                            break;
                        }
                    }
                }

                SourceNode::List { inner, range } => {
                    new.push(SourceNode::List {
                        inner: lower_tree(inner),
                        range,
                    });
                }

                SourceNode::Quoted { mut inner, range } => {
                    *inner = lower_tree_quoted(*inner);
                    new.push(SourceNode::Quoted { inner, range });
                }

                SourceNode::Atom { .. } => {
                    new.push(item);
                }
            }
        }

        return new.into_boxed_slice();
    }
}

fn lower_tree_quoted(node: SourceNode) -> SourceNode {
    match node {
        SourceNode::Atom { .. } => node,

        SourceNode::Quoted { mut inner, range } => {
            *inner = lower_tree_quoted(*inner);
            SourceNode::Quoted { inner, range }
        }

        SourceNode::List { inner, range } => SourceNode::List {
            inner: lower_tree(inner),
            range,
        },

        SourceNode::Cons { .. } => panic!("unexpected cons"),
    }
}

impl SourceNode {
    pub fn synth_atom(kind: AtomKind, span: impl AsRef<str>) -> Self {
        Self::Atom {
            kind,
            atom: Atom::new(span),
            pos: Default::default(),
        }
    }

    pub fn synth_list(inner: Box<[SourceNode]>) -> Self {
        Self::List {
            inner,
            range: Default::default(),
        }
    }

    pub fn range(&self) -> ByteRange {
        match self {
            SourceNode::Atom {
                kind: AtomKind::String,
                pos,
                atom,
                ..
            } => {
                if pos.is_undefined() {
                    ByteRange::default()
                } else {
                    // Offset double quotes
                    ByteRange {
                        lo: *pos - 1,
                        hi: *pos + 1 + atom.len() as u32,
                    }
                }
            }

            SourceNode::Atom { pos, atom, .. } => {
                if pos.is_undefined() {
                    ByteRange::default()
                } else {
                    ByteRange {
                        lo: *pos,
                        hi: *pos + atom.len() as u32,
                    }
                }
            }

            SourceNode::List { range, .. }
            | SourceNode::Cons { range, .. }
            | SourceNode::Quoted { range, .. } => {
                if range.lo.is_undefined() {
                    ByteRange::default()
                } else {
                    *range
                }
            }
        }
    }

    pub fn is_trivia(&self) -> bool {
        match self {
            SourceNode::Atom {
                kind: AtomKind::Comment,
                ..
            } => true,
            SourceNode::Atom {
                kind: AtomKind::Whitespace,
                ..
            } => true,
            _ => false,
        }
    }

    pub fn is_list(&self) -> bool {
        matches!(self, SourceNode::List { .. })
    }

    pub fn is_whitespace(&self) -> bool {
        matches!(
            self,
            SourceNode::Atom {
                kind: AtomKind::Whitespace,
                ..
            }
        )
    }

    pub fn as_list(&self) -> Option<&[SourceNode]> {
        if let SourceNode::List { inner, .. } = self {
            Some(inner)
        } else {
            None
        }
    }

    // TODO: Unify this with const generics
    pub fn as_string(&self) -> Option<&Atom> {
        if let SourceNode::Atom {
            atom,
            kind: AtomKind::String,
            ..
        } = self
        {
            Some(atom)
        } else {
            None
        }
    }

    pub fn as_symbol(&self) -> Option<&Atom> {
        if let SourceNode::Atom {
            atom,
            kind: AtomKind::Symbol,
            ..
        } = self
        {
            Some(atom)
        } else {
            None
        }
    }

    pub fn as_kind_string(&self) -> String {
        match self {
            SourceNode::Atom {
                kind: AtomKind::Bool,
                ..
            } => format!("boolean"),
            SourceNode::Atom {
                kind: AtomKind::Symbol,
                ..
            } => format!("symbol"),
            SourceNode::Atom {
                kind: AtomKind::Number,
                ..
            } => format!("number"),
            SourceNode::Atom {
                kind: AtomKind::String,
                ..
            } => format!("string"),
            SourceNode::Atom {
                kind: AtomKind::Comment,
                ..
            } => format!("comment"),
            SourceNode::Atom {
                kind: AtomKind::Whitespace,
                ..
            } => format!("whitespace"),
            SourceNode::Cons { .. } => format!("improper list"),
            SourceNode::Quoted { inner, .. } => format!("quoted {}", inner.as_kind_string()),
            SourceNode::List { inner, .. } => {
                if inner.is_empty() {
                    format!("list")
                } else {
                    format!("empty list")
                }
            }
        }
    }

    pub fn without_location(&self) -> Self {
        match self {
            SourceNode::Atom { kind, atom, .. } => SourceNode::Atom {
                kind: *kind,
                atom: atom.clone(),
                pos: Default::default(),
            },

            SourceNode::List { inner, .. } => SourceNode::List {
                inner: inner.iter().map(Self::without_location).collect(),
                range: Default::default(),
            },

            SourceNode::Cons { inner, .. } => SourceNode::Cons {
                inner: inner.iter().map(Self::without_location).collect(),
                range: Default::default(),
            },

            SourceNode::Quoted { inner, .. } => SourceNode::Quoted {
                inner: Box::new(inner.without_location()),
                range: Default::default(),
            },
        }
    }

    fn span_of_kind<'s>(kind: AtomKind) -> impl Fn(Span<'s>) -> SourceNode {
        move |span| SourceNode::Atom {
            kind,
            atom: Atom::new(span.fragment()),
            pos: (span.location_offset() as u32).into(),
        }
    }
}

impl Display for SourceNode {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> fmt::Result {
        match self {
            SourceNode::Atom {
                kind: AtomKind::String,
                atom,
                ..
            } => {
                write!(fmt, "\"{}\"", atom)?;
            }

            SourceNode::Atom { atom, .. } => {
                write!(fmt, "{}", atom)?;
            }

            SourceNode::List { inner, .. } => {
                write!(fmt, "(")?;
                for node in inner.iter() {
                    write!(fmt, "{}", node)?;
                }
                write!(fmt, ")")?;
            }

            SourceNode::Cons { inner, .. } => {
                write!(fmt, ".")?;
                for node in inner.iter() {
                    write!(fmt, "{}", node)?;
                }
            }

            SourceNode::Quoted { inner, .. } => {
                write!(fmt, "'{}", inner)?;
            }
        };

        Ok(())
    }
}

// #[macro_export]
// macro_rules! format_list {
//     ($fmt:expr, $pat:literal, $iter:expr) => {{
//         format_list!($fmt, "(", $pat, $iter, ")")
//     }};

//     ($fmt:expr, $pat:literal, $iter:expr, $last:expr) => {{
//         format_list!($fmt, "(", $pat, $iter, concat!(" . ", $pat, ")"), $last)
//     }};

//     ($fmt:expr, $open:literal, $pat:literal, $iter:expr, $close:expr $( , $last:expr )*) => {{
//         write!($fmt, $open)?;

//         let mut values = $iter;
//         if let Some(first) = values.next() {
//             write!($fmt, $pat, first)?;

//             for next in values {
//                 write!($fmt, concat!(" ", $pat), next)?;
//             }
//         }

//         write!($fmt, $close, $( $last )*)
//     }};
// }

#[cfg(test)]
mod tests {
    use super::*;

    fn span<'s>(input: &'s str) -> Span<'s> {
        Span::new(input)
    }

    #[test]
    fn test_size() {
        assert_eq!(std::mem::size_of::<SourceNode>(), 32);
    }

    #[test]
    fn test_sep0() {
        let (nxt, val) = sep0(span(" ; a comment \r\nxx")).unwrap();

        assert_eq!(nxt.fragment(), &"xx");

        assert_eq!(
            val,
            vec![
                SourceNode::Atom {
                    kind: AtomKind::Whitespace,
                    atom: " ".into(),
                    pos: 0.into(),
                },
                SourceNode::Atom {
                    kind: AtomKind::Comment,
                    atom: "; a comment \r\n".into(),
                    pos: 1.into(),
                },
            ]
        );
    }

    #[test]
    fn test_parse_bool() {
        let (nxt, val) = parse_bool(span("#t ")).unwrap();

        assert_eq!(nxt.fragment(), &" ");

        assert_eq!(
            val,
            SourceNode::Atom {
                kind: AtomKind::Bool,
                atom: "#t".into(),
                pos: 0.into(),
            }
        );

        let (_, val) = parse_bool(span("#f ")).unwrap();
        assert_eq!(
            val,
            SourceNode::Atom {
                kind: AtomKind::Bool,
                atom: "#f".into(),
                pos: 0.into(),
            }
        );

        assert!(parse_bool(span("#x ")).is_err());
    }

    #[test]
    fn test_parse_symbol() {
        let (nxt, val) = parse_symbol(span("+~->$%* ")).unwrap();

        assert_eq!(nxt.fragment(), &" ");

        assert_eq!(
            val,
            SourceNode::Atom {
                kind: AtomKind::Symbol,
                atom: "+~->$%*".into(),
                pos: 0.into(),
            }
        );

        let (_, val) = parse_symbol(span("slope ")).unwrap();
        assert_eq!(
            val,
            SourceNode::Atom {
                kind: AtomKind::Symbol,
                atom: "slope".into(),
                pos: 0.into(),
            }
        );

        let (_, val) = parse_symbol(span("λaμb1 ")).unwrap();
        assert_eq!(
            val,
            SourceNode::Atom {
                kind: AtomKind::Symbol,
                atom: "λaμb1".into(),
                pos: 0.into(),
            }
        );

        assert!(parse_symbol(span("1a")).is_err());
        // assert!(parse_symbol(span(".")).is_err());
        assert!(parse_symbol(span(";")).is_err());
        assert!(parse_symbol(span("'")).is_err());
    }

    #[test]
    fn test_parse_number() {
        let (_, val) = parse_number(span("-12315 ")).unwrap();
        assert_eq!(
            val,
            SourceNode::Atom {
                kind: AtomKind::Number,
                atom: "-12315".into(),
                pos: 0.into(),
            }
        );

        let (_, val) = parse_number(span("-12.315 ")).unwrap();
        assert_eq!(
            val,
            SourceNode::Atom {
                kind: AtomKind::Number,
                atom: "-12.315".into(),
                pos: 0.into(),
            }
        );

        let (_, val) = parse_number(span("-12112121213213112315 ")).unwrap();
        assert_eq!(
            val,
            SourceNode::Atom {
                kind: AtomKind::Number,
                atom: "-12112121213213112315".into(),
                pos: 0.into(),
            }
        );

        assert!(parse_number(span("+-1.23")).is_err());
    }

    #[test]
    fn test_parse_string() {
        let (_, val) = parse_string(span("\"\" ")).unwrap();
        assert_eq!(
            val,
            SourceNode::Atom {
                kind: AtomKind::String,
                atom: "".into(),
                pos: 1.into(),
            }
        );

        let (_, val) = parse_string(span("\" \" ")).unwrap();
        assert_eq!(
            val,
            SourceNode::Atom {
                kind: AtomKind::String,
                atom: " ".into(),
                pos: 1.into(),
            }
        );

        let (_, val) = parse_string(span("\"foo bar\" ")).unwrap();
        assert_eq!(
            val,
            SourceNode::Atom {
                kind: AtomKind::String,
                atom: "foo bar".into(),
                pos: 1.into(),
            }
        );

        let (_, val) = parse_string(span("\"ἓν οἶδα ὅτι οὐδὲν οἶδα\"")).unwrap();
        assert_eq!(
            val,
            SourceNode::Atom {
                kind: AtomKind::String,
                atom: "ἓν οἶδα ὅτι οὐδὲν οἶδα".into(),
                pos: 1.into(),
            }
        );

        let (_, val) = parse_string(span(r#""\"'\\foo\n\r\t~\"" "#)).unwrap();
        assert_eq!(
            val,
            SourceNode::Atom {
                kind: AtomKind::String,
                atom: r#"\"'\\foo\n\r\t~\""#.into(),
                pos: 1.into(),
            }
        );

        assert!(parse_string(span("'foo bar'")).is_err());
    }

    #[test]
    fn test_parse_list() {
        assert!(parse_list(0)(span("( ")).is_err());

        assert!(parse_list(0)(span("( \t\r\n ")).is_err());

        let (_, val) = parse_list(0)(span("(  )")).unwrap();
        assert_eq!(
            val,
            SourceNode::List {
                inner: Box::new([SourceNode::Atom {
                    kind: AtomKind::Whitespace,
                    atom: "  ".into(),
                    pos: 1.into(),
                },]),
                range: ByteRange {
                    lo: 0.into(),
                    hi: 4.into(),
                },
            }
        );

        let (_, val) = parse_list(0)(span("(1.3  foo)")).unwrap();
        assert_eq!(
            val,
            SourceNode::List {
                inner: Box::new([
                    SourceNode::Atom {
                        kind: AtomKind::Number,
                        atom: "1.3".into(),
                        pos: 1.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Whitespace,
                        atom: "  ".into(),
                        pos: 4.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Symbol,
                        atom: "foo".into(),
                        pos: 6.into(),
                    },
                ]),
                range: ByteRange {
                    lo: 0.into(),
                    hi: 10.into(),
                },
            }
        );

        let (_, val) = parse_list(0)(span("(1 . 2)")).unwrap();
        assert_eq!(
            val,
            SourceNode::List {
                inner: Box::new([
                    SourceNode::Atom {
                        kind: AtomKind::Number,
                        atom: "1".into(),
                        pos: 1.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Whitespace,
                        atom: " ".into(),
                        pos: 2.into(),
                    },
                    SourceNode::Cons {
                        inner: Box::new([
                            SourceNode::Atom {
                                kind: AtomKind::Whitespace,
                                atom: " ".into(),
                                pos: 4.into(),
                            },
                            SourceNode::Atom {
                                kind: AtomKind::Number,
                                atom: "2".into(),
                                pos: 5.into(),
                            },
                        ]),
                        range: (3..6).into(),
                    },
                ]),
                range: (0..7).into(),
            }
        );

        let (_, val) = parse_list(0)(span("( 1 2 foo ;; comment \t\r\n 3.14 )")).unwrap();
        assert_eq!(
            val,
            SourceNode::List {
                inner: Box::new([
                    SourceNode::Atom {
                        kind: AtomKind::Whitespace,
                        atom: " ".into(),
                        pos: 1.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Number,
                        atom: "1".into(),
                        pos: 2.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Whitespace,
                        atom: " ".into(),
                        pos: 3.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Number,
                        atom: "2".into(),
                        pos: 4.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Whitespace,
                        atom: " ".into(),
                        pos: 5.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Symbol,
                        atom: "foo".into(),
                        pos: 6.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Whitespace,
                        atom: " ".into(),
                        pos: 9.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Comment,
                        atom: ";; comment \t\r\n".into(),
                        pos: 10.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Whitespace,
                        atom: " ".into(),
                        pos: 24.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Number,
                        atom: "3.14".into(),
                        pos: 25.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Whitespace,
                        atom: " ".into(),
                        pos: 29.into(),
                    },
                ]),
                range: (0..31).into(),
            }
        );

        let (_, val) = parse_list(0)(span("( 1 2 foo . bar )")).unwrap();
        assert_eq!(
            val,
            SourceNode::List {
                inner: Box::new([
                    SourceNode::Atom {
                        kind: AtomKind::Whitespace,
                        atom: " ".into(),
                        pos: 1.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Number,
                        atom: "1".into(),
                        pos: 2.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Whitespace,
                        atom: " ".into(),
                        pos: 3.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Number,
                        atom: "2".into(),
                        pos: 4.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Whitespace,
                        atom: " ".into(),
                        pos: 5.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Symbol,
                        atom: "foo".into(),
                        pos: 6.into(),
                    },
                    SourceNode::Atom {
                        kind: AtomKind::Whitespace,
                        atom: " ".into(),
                        pos: 9.into(),
                    },
                    SourceNode::Cons {
                        inner: Box::new([
                            SourceNode::Atom {
                                kind: AtomKind::Whitespace,
                                atom: " ".into(),
                                pos: 11.into(),
                            },
                            SourceNode::Atom {
                                kind: AtomKind::Symbol,
                                atom: "bar".into(),
                                pos: 12.into(),
                            },
                            SourceNode::Atom {
                                kind: AtomKind::Whitespace,
                                atom: " ".into(),
                                pos: 15.into(),
                            },
                        ]),
                        range: (10..16).into(),
                    },
                ]),
                range: (0..17).into(),
            }
        );
    }

    #[test]
    fn test_parse_lossless() {
        assert!(parse_lossless("'").next().unwrap().is_err());

        assert!(parse_lossless("( ; comment \t\r\n\t ")
            .next()
            .unwrap()
            .is_err());

        let val = parse_lossless("; comment").next().unwrap().unwrap();
        assert_eq!(
            val,
            SourceNode::Atom {
                kind: AtomKind::Comment,
                atom: "; comment".into(),
                pos: 0.into(),
            }
        );

        // let (_, val) = parse_expression("''( )").unwrap();
        // assert_eq!(
        //     val,
        //     SourceNode {
        //         value: SourceValue::Quoted(Box::new(SourceNode {
        //             value: SourceValue::Quoted(Box::new(SourceNode {
        //                 value: SourceValue::ProperList(Box::new([])),
        //                 range: Location { line: 1, col: 3 }..Location { line: 1, col: 6 },
        //             })),
        //             range: Location { line: 1, col: 2 }..Location { line: 1, col: 6 },
        //         })),
        //         range: Location { line: 1, col: 1 }..Location { line: 1, col: 6 },
        //     }
        // );

        //         let (_, val) = parse_expression("( + 1 2.0 'foo ''bar )", &mut E).unwrap();
        //         assert_deep_eq!(
        //             val,
        //             list!(E =>
        //                 E.symbol("+"),
        //                 E.number("1"),
        //                 E.number("2.0"),
        //                 E.quote(E.symbol("foo")),
        //                 E.quote(E.quote(E.symbol("bar"))),
        //             )
        //         );

        //         let (_, val) = parse_expression("( 1 ;; a comment\r\n2.0 'foo )", &mut E).unwrap();
        //         assert_deep_eq!(
        //             val,
        //             list!(E.number("1"), E.number("2.0"), E.quote(E.symbol("foo")),)
        //         );
        //     }

        //     fn collect(items: impl Iterator<Item = Result<Value, ParseError>>) -> Vec<Value> {
        //         items.map(Result::unwrap).collect::<Vec<_>>()
        //     }

        //     #[test]
        //     fn test_parse() {
        //         let vals = collect(parse("1.123 ;;; ", &mut E));
        //         assert_eq!(vals, vec![E.number("1.123")]);

        //         let vals = collect(parse("1.123 ;;; \r\n", &mut E));
        //         assert_eq!(vals, vec![E.number("1.123")]);

        //         let res = parse("foo----", &mut E).next().unwrap();
        //         assert_eq!(res.unwrap_err().what, ErrorKind::ExpectedSpace);

        //         let res = parse("(foo)----", &mut E).next().unwrap();
        //         assert_eq!(res.unwrap_err().what, ErrorKind::ExpectedSpace);

        //         let res = parse("(", &mut E).next().unwrap();
        //         assert_eq!(res.unwrap_err().what, ErrorKind::Incomplete);

        //         let res = parse("'''", &mut E).next().unwrap();
        //         assert_eq!(res.unwrap_err().what, ErrorKind::InvalidExpression);

        //         let res = parse("('')", &mut E).next().unwrap();
        //         assert_eq!(res.unwrap_err().what, ErrorKind::InvalidExpression);

        //         let res = parse(" ( foo 1.1 '()", &mut E).next().unwrap();
        //         assert_eq!(res.unwrap_err().what, ErrorKind::Incomplete);

        //         let res = parse(" ( foo 1.1 '() ; ; comment", &mut E).next().unwrap();
        //         assert_eq!(res.unwrap_err().what, ErrorKind::Incomplete);

        //         let res = parse(" ( foo 1.1 ) ( bar '", &mut E).collect::<Vec<_>>();
        //         assert_deep_eq!(
        //             *res[0].as_ref().unwrap(),
        //             list!(E.symbol("foo"), E.number("1.1"))
        //         );
        //         assert_eq!(
        //             res[1],
        //             Err(ParseError {
        //                 what: ErrorKind::Incomplete,
        //                 line: 1,
        //                 column: 21,
        //             })
        //         );
    }

    #[test]
    fn test_lower_cons_pair_list() {
        let (_, list) = parse_list(0)(span("(1 . (2 . (3 . ())))")).unwrap();
        let list = if let SourceNode::List { inner, .. } = list {
            inner
        } else {
            panic!("not a list");
        };

        let list = lower_tree(list);
        assert_eq!(
            &*list,
            &[
                SourceNode::Atom {
                    kind: AtomKind::Number,
                    atom: "1".into(),
                    pos: 1.into(),
                },
                SourceNode::Atom {
                    kind: AtomKind::Number,
                    atom: "2".into(),
                    pos: 6.into(),
                },
                SourceNode::Atom {
                    kind: AtomKind::Number,
                    atom: "3".into(),
                    pos: 11.into(),
                },
            ]
        );
    }

    #[test]
    fn test_lower_nested_improper_list() {
        let (_, list) = parse_list(0)(span("(1 . (2 . 3))")).unwrap();
        let list = if let SourceNode::List { inner, .. } = list {
            inner
        } else {
            panic!("not a list");
        };

        let list = lower_tree(list);
        assert_eq!(
            &*list,
            &[
                SourceNode::Atom {
                    kind: AtomKind::Number,
                    atom: "1".into(),
                    pos: 1.into(),
                },
                SourceNode::Atom {
                    kind: AtomKind::Number,
                    atom: "2".into(),
                    pos: 6.into(),
                },
                SourceNode::Cons {
                    inner: Box::new([SourceNode::Atom {
                        kind: AtomKind::Number,
                        atom: "3".into(),
                        pos: 10.into(),
                    }]),
                    range: Default::default(),
                },
            ]
        );
    }

    #[test]
    fn test_large_input() {
        let input = " ".repeat(limit::MAX_LENGTH as usize + 1);
        let err = parse_lossless(&input)
            .collect::<Vec<_>>()
            .pop()
            .unwrap()
            .unwrap_err();

        assert_eq!(
            err,
            ParseError {
                kind: ParseErrorKind::InputTooLarge,
                origin: Default::default(),
            }
        )
    }

    #[test]
    fn test_only_open() {
        // Increase in stack size should be only needed for development.
        let input = "(".repeat(limit::MAX_DEPTH as usize + 1);
        let err = parse_lossless(&input).next().unwrap().unwrap_err();

        assert_eq!(
            err,
            ParseError {
                kind: ParseErrorKind::MaximumExpressionDepth,
                origin: Default::default(),
            }
        )
    }

    #[test]
    fn test_only_quote() {
        // Increase in stack size should be only needed for development.
        let input = "'".repeat(limit::MAX_DEPTH as usize + 1);
        let err = parse_lossless(&input).next().unwrap().unwrap_err();
        assert_eq!(
            err,
            ParseError {
                kind: ParseErrorKind::MaximumExpressionDepth,
                origin: Default::default(),
            }
        )
    }
}
