use std::{env, fs, sync::mpsc, thread};

use ereq::MSO;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: ereq <file.mona>");
        std::process::exit(1);
    }

    let input = fs::read_to_string(&args[1]).unwrap_or_else(|e| {
        eprintln!("error reading {}: {}", args[1], e);
        std::process::exit(1);
    });

    const STACK_SIZE: usize = 512 * 1024 * 1024;
    let (tx, rx) = mpsc::channel();

    thread::Builder::new()
        .name("solver".into())
        .stack_size(STACK_SIZE)
        .spawn(move || {
            let mut mso: MSO = MSO::new();
            let node = mso.parse_mona_m2l_str(&input).expect("failed to parse");
            let is_empty = mso.b().is_empty_lang(node);
            tx.send(is_empty)
        })
        .unwrap();

    let is_empty = rx.recv().unwrap();
    if is_empty {
        println!("unsat");
    } else {
        println!("sat");
    }
}
