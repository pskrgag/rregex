mod dfa;
mod nfa;
mod regex;

#[cfg(test)]
mod helper;

fn main() {
    let mut nfa = regex::compile_regex("c(a|b)");

    assert!(nfa.run(&['c', 'b']));
    assert!(nfa.run(&['c', 'a']));
    assert!(!nfa.run(&['c', 'a', 'a']));
}
