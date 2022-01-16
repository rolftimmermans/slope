use std::{
    env,
    fs::{read_dir, read_to_string, File},
    io::{Error, Write},
    path::PathBuf,
};

use regex::Regex;

fn main() {
    let target: PathBuf = env::var_os("OUT_DIR").unwrap().into();
    let mut output = File::create(target.join("generated.rs")).unwrap();

    println!("cargo:rerun-if-changed=tests");
    for entry in read_dir("tests/").unwrap() {
        if let Ok(entry) = entry {
            if let Some(ext) = entry.path().extension() {
                if ext == "sl" {
                    println!("cargo:rerun-if-changed={}", entry.path().display());
                    write_tests(&mut output, entry.path()).unwrap();
                }
            }
        }
    }
}

fn write_tests(output: &mut File, path: PathBuf) -> Result<(), Error> {
    let source = read_to_string(&path).unwrap();

    for (i, source) in source.split("; ---\n").enumerate() {
        let source = source.trim();

        if source.is_empty() {
            continue;
        }

        let (name, assertion) = extract_attributes(source);

        if let Assertion::None = assertion {
            continue;
        }

        let test_group = path.file_stem().unwrap().to_string_lossy();
        let test_name = if let Some(name) = name {
            format!("test_{}_{}", test_group, name.replace(" ", "_"))
        } else {
            format!("test_{}_{}", test_group, i)
        };

        writeln!(output)?;
        writeln!(output, "#[test]")?;
        writeln!(output, "fn {}() {{", test_name)?;
        writeln!(output, "    use slope_vm::VirtualMachine;")?;
        writeln!(output, "    let _ = simple_logger::init();")?;
        writeln!(output, "    let mut vm = VirtualMachine::default();")?;
        writeln!(output, "    let res = vm.evaluate({:?});", source)?;
        write_assertion(output, assertion)?;
        writeln!(output, "}}")?;
    }

    Ok(())
}

fn write_assertion(output: &mut File, assertion: Assertion) -> Result<(), Error> {
    match assertion {
        Assertion::Result(exp_result) => {
            writeln!(output, "    if let Err(err) = res {{")?;
            writeln!(output, "        panic!(\"evaluation failed: {{}}\", err);")?;
            writeln!(output, "    }}")?;
            writeln!(
                output,
                "    assert_eq!({:?}, vm.result().to_string());",
                exp_result
            )?;
        }

        Assertion::Error(exp_error) => {
            writeln!(
                output,
                "    assert_eq!({:?}, res.unwrap_err().to_string());",
                exp_error
            )?;
            writeln!(output, "    assert_eq!(\"nil\", vm.result().to_string());")?;
        }

        Assertion::None => {}
    }

    Ok(())
}

#[derive(Debug)]
enum Assertion {
    Result(String),
    Error(String),
    None,
}

fn extract_match(regex: Regex, input: &str) -> Option<String> {
    let mut buf = String::new();

    if let Some(cap) = regex.captures(input) {
        for sub in cap.iter().skip(1) {
            if let Some(sub) = sub {
                buf += sub.as_str();
            }
        }

        Some(buf)
    } else {
        None
    }
}

fn extract_attributes(input: &str) -> (Option<String>, Assertion) {
    let name_re = Regex::new(r"^;[ ]+(.*)\n").unwrap();
    let result_re = Regex::new(r"(?m)^;[ ]+result:[ ]+(.*)$").unwrap();
    let error_re = Regex::new(r"(?m)^;[ ]+error: (.*)$*").unwrap();

    let name = extract_match(name_re, input);

    if let Some(result) = extract_match(result_re, input) {
        (name, Assertion::Result(result))
    } else if let Some(error) = extract_match(error_re, input) {
        (name, Assertion::Error(error))
    } else {
        (name, Assertion::None)
    }
}
