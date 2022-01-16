use slope::{exec, panic_handler, repl};
use std::{env, panic};

fn main() {
    panic::set_hook(Box::new(panic_handler));

    if env::args().count() > 1 {
        exec().unwrap();
    } else {
        repl().unwrap();
    }
}
