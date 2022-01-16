use super::{ExpressionValidator, MatchingBracketHighlighter};
use rustyline::{
    highlight::Highlighter,
    validate::{ValidationContext, ValidationResult, Validator},
    Result,
};
use rustyline_derive::{Completer, Helper, Hinter};
use std::borrow::Cow::{self, Borrowed, Owned};

#[derive(Completer, Hinter, Helper)]
pub struct ReplHelper {
    pub validator: ExpressionValidator,
    pub highlighter: MatchingBracketHighlighter,
    pub colored_prompt: String,
}

impl Validator for ReplHelper {
    fn validate(&self, ctx: &mut ValidationContext) -> Result<ValidationResult> {
        self.validator.validate(ctx)
    }

    fn validate_while_typing(&self) -> bool {
        self.validator.validate_while_typing()
    }
}

impl Highlighter for ReplHelper {
    fn highlight_prompt<'b, 's: 'b, 'p: 'b>(
        &'s self,
        prompt: &'p str,
        default: bool,
    ) -> Cow<'b, str> {
        if default {
            Borrowed(&self.colored_prompt)
        } else {
            Borrowed(prompt)
        }
    }

    fn highlight_hint<'h>(&self, hint: &'h str) -> Cow<'h, str> {
        Owned("\x1b[1m".to_owned() + hint + "\x1b[m")
    }

    fn highlight<'l>(&self, line: &'l str, pos: usize) -> Cow<'l, str> {
        self.highlighter.highlight(line, pos)
    }

    fn highlight_char(&self, line: &str, pos: usize) -> bool {
        self.highlighter.highlight_char(line, pos)
    }
}
