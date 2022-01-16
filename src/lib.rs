mod repl;

use slope_vm::{ByteRange, Error, VirtualMachine};

use termcolor::{Color, ColorChoice, ColorSpec, StandardStream, WriteColor};

use repl::{Repl, ReplError};

use std::{
    env::args,
    fs::read_to_string,
    io::{self, Write},
    panic::PanicInfo,
};

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

static PRELUDE: &str = include_str!("std/prelude.sl");

pub fn repl() -> io::Result<()> {
    let mut vm = VirtualMachine::default();
    vm.load_prelude(PRELUDE).expect("loading prelude failed");

    let mut repl = Repl::default();

    let stdout = &mut StandardStream::stdout(ColorChoice::Auto);
    let stderr = &mut StandardStream::stderr(ColorChoice::Auto);

    loop {
        let readline = repl.readline();

        match readline {
            Ok(line) => {
                repl.add_history_entry(line.as_str());

                if let Err(err) = vm.evaluate(&line) {
                    write_error(stderr, err, line.as_str(), "<repl>")?;
                } else {
                    writeln!(stdout, "{}", vm.result())?;
                }
            }

            Err(ReplError::Interrupted) | Err(ReplError::Eof) => {
                writeln!(stdout, "Bye!")?;
                break;
            }

            Err(err) => {
                writeln!(stderr, "\x1b[1;31mError:\x1b[0m {}", err)?;
                break;
            }
        }
    }

    repl.save_history().unwrap();
    Ok(())
}

pub fn exec() -> io::Result<()> {
    let mut vm = VirtualMachine::default();
    vm.load_prelude(PRELUDE).expect("loading prelude failed");

    let stdout = &mut StandardStream::stdout(ColorChoice::Auto);
    let stderr = &mut StandardStream::stderr(ColorChoice::Auto);

    for arg in args().skip(1) {
        match vm.evaluate(&read_to_string(arg).unwrap()) {
            Ok(()) => {
                writeln!(stdout, "{}", vm.result())?;
            }

            Err(err) => {
                write_error(stderr, err, "", "<repl>")?;
            }
        }
    }

    Ok(())
}

fn write_error(out: &mut StandardStream, err: Error, _input: &str, _file: &str) -> io::Result<()> {
    if let Some(ByteRange { hi, lo }) = err.origin() {
        println!("{} {}", hi, lo);
        // let columns = (end.col - start.col) as usize;

        // if let Some(line) = input.lines().nth(start.line as usize - 1) {
        //     out.set_color(ColorSpec::new().set_fg(Some(Color::Red)).set_bold(true))?;
        //     write!(out, "error")?;
        //     out.reset()?;
        //     writeln!(
        //         out,
        //         ": {err} in {file} at {line}:{col}",
        //         file = file,
        //         line = start.line,
        //         col = start.col,
        //         err = err,
        //     )?;

        //     out.set_color(ColorSpec::new().set_fg(Some(Color::Blue)).set_bold(true))?;
        //     writeln!(out, "     | ")?;
        //     write!(out, "{line:>4} | ", line = start.line)?;
        //     out.reset()?;
        //     writeln!(out, "{}", line)?;

        //     out.set_color(ColorSpec::new().set_fg(Some(Color::Blue)).set_bold(true))?;
        //     write!(out, "     |")?;
        //     out.set_color(ColorSpec::new().set_fg(Some(Color::Red)).set_bold(true))?;
        //     let carets: String = repeat('^').take(columns).collect();
        //     writeln!(
        //         out,
        //         "{carets:>end$}",
        //         carets = carets,
        //         end = end.col as usize,
        //     )?;
        //     out.reset()?;

        //     if let Some(hint) = err.hint() {
        //         out.set_color(ColorSpec::new().set_fg(Some(Color::Cyan)).set_bold(true))?;
        //         write!(out, " hint")?;
        //         out.reset()?;
        //         writeln!(out, ": {hint}", hint = hint)?;
        //     }

        //     writeln!(out, "")?;
        // }
    } else {
        writeln!(out, "{}", err)?;
    }

    Ok(())
}

pub fn panic_handler(info: &PanicInfo) {
    // Don't try to unwrap errors here, there's no point.
    let out = &mut StandardStream::stderr(ColorChoice::Auto);
    let _ = out.set_color(ColorSpec::new().set_fg(Some(Color::Magenta)).set_bold(true));
    let _ = write!(out, "crash");
    let _ = out.reset();
    let _ = write!(out, ": assertion failed");

    if let Some(loc) = info.location() {
        let _ = write!(out, " at {}:{}", loc.file(), loc.line());
    }

    if let Some(msg) = info.payload().downcast_ref::<String>() {
        let _ = write!(out, ": {}", msg);
    } else if let Some(msg) = info.payload().downcast_ref::<&str>() {
        let _ = write!(out, ": {}", msg);
    }

    let _ = writeln!(out);

    let _ = out.set_color(ColorSpec::new().set_fg(Some(Color::Cyan)).set_bold(true));
    let _ = write!(out, " note");
    let _ = out.reset();
    let _ = writeln!(out, ": this is a bug!");
    let _ = writeln!(out);
}
