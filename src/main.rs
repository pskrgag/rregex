use std::env;

mod dfa;
mod nfa;
mod regex;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 3 {
        eprintln!("Usage: {} <regex> <string>\n", args[0]);
    } else {
        if let Some(mut nfa) = regex::compile_regex(args[1].as_str()) {
            if nfa.run(args[2].as_str()) {
                println!("Matches!");
            } else {
                println!("Does not match!");
            }
        } else {
            eprintln!("Failed to compile regex");
        }
    }
}
