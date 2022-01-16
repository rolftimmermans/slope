

use rustyline::{
    validate::{ValidationContext, ValidationResult, Validator},
    Result,
};

#[derive(Default)]
pub struct ExpressionValidator;

impl Validator for ExpressionValidator {
    fn validate(&self, _ctx: &mut ValidationContext) -> Result<ValidationResult> {
        // match self.vm.validate(ctx.input()) {
        //     Err(err) if err.is_incomplete() => return Ok(ValidationResult::Incomplete),
        //     //Err(..) => return Ok(ValidationResult::Invalid(Some("parse error".to_owned()))),
        //     Err(..) => (),
        //     Ok(..) => (),
        // }

        Ok(ValidationResult::Valid(None))
    }

    fn validate_while_typing(&self) -> bool {
        false
    }
}
