mod helper;
mod highlight;
mod validate;

use helper::ReplHelper;
use highlight::MatchingBracketHighlighter;
use validate::ExpressionValidator;

use dirs;
use rustyline::{Config, Editor};

pub use rustyline::error::ReadlineError as ReplError;

const HIST_FILE: &str = ".slope_history";

pub struct Repl {
    editor: Editor<ReplHelper>,
}

impl Default for Repl {
    fn default() -> Self {
        let config = Config::builder().history_ignore_space(true).build();

        let mut editor = Editor::with_config(config);
        editor.set_helper(Some(ReplHelper {
            highlighter: MatchingBracketHighlighter::default(),
            validator: ExpressionValidator::default(),
            colored_prompt: "\x1b[1;93m>> \x1b[0m".to_owned(),
        }));

        if let Some(mut hist) = dirs::home_dir() {
            hist.push(HIST_FILE);

            if editor.load_history(&hist).is_err() {
                println!("(No previous history)");
            }
        } else {
            println!("(No home directory found; history will not be saved)");
        }

        Repl { editor }
    }
}

impl Repl {
    pub fn readline(&mut self) -> Result<String, ReplError> {
        self.editor.readline(">> ")
    }

    pub fn add_history_entry(&mut self, line: &str) -> bool {
        self.editor.add_history_entry(line)
    }

    pub fn save_history(&mut self) -> Result<(), ReplError> {
        if let Some(mut hist) = dirs::home_dir() {
            hist.push(HIST_FILE);

            self.editor.save_history(&hist)
        } else {
            Ok(())
        }
    }
}
