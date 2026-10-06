use std::env;
use std::process;

fn main() {
    let mut args = env::args().skip(1);
    let Some(path) = args.next() else {
        eprintln!("pagurus: statically diagnose ownership errors in a small C subset");
        eprintln!();
        eprintln!("Usage: pagurus <file.c>");
        process::exit(2);
    };

    match pagurus::check_file(&path) {
        Ok(diags) => {
            for diag in &diags {
                eprint!("{diag}");
            }
            if !diags.is_empty() {
                process::exit(1);
            }
        }
        Err(err) => {
            eprintln!("error: {err}");
            process::exit(2);
        }
    }
}
