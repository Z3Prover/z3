use std::io::prelude::*;
use std::process::{Command, Stdio};

static HELLO_Z3: &'static str =
"(echo \"hello from z3\")\n";

fn main() {
    // Spawn the `z3` command
    let process = match Command::new("z3").arg("-in").arg("-smt2")
                                .stdin(Stdio::piped())
                                .stdout(Stdio::piped())
                                .spawn() {
        Err(why) => panic!("couldn't spawn z3: {}", why),
        Ok(process) => process,
    };

    match process.stdin.unwrap().write_all(HELLO_Z3.as_bytes()) {
        Err(why) => panic!("couldn't write to z3 stdin: {}", why),
        Ok(_) => println!("sent to z3"),
    }

    let mut s = String::new();
    match process.stdout.unwrap().read_to_string(&mut s) {
        Err(why) => panic!("couldn't read wc stdout: {}", why),
        Ok(_) => print!("z3 responded with:\n{}", s),
    }
}
