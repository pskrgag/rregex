use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

pub type State = usize;
pub type Transtions<T> = HashMap<(State, T), State>;

pub struct Dfa<T> {
    transitions: Transtions<T>,
    start: State,
    accepting: Vec<State>,
}

impl<T: Eq + Hash + Copy> Dfa<T> {
    fn new(transitions: Transtions<T>, start: State, accepting: Vec<State>) -> Self {
        Self {
            transitions,
            start,
            accepting,
        }
    }

    pub fn run(&mut self, input: &[T]) -> bool {
        let mut current = self.start;

        for i in input.into_iter() {
            if let Some(next) = self.transitions.get(&(current, *i)) {
                current = *next;
            } else {
                return false;
            }
        }

        self.accepting.iter().find(|x| **x == current).is_some()
    }
}

#[allow(dead_code)]
#[cfg(test)]
impl<T: Eq + Hash + Copy + Debug> Dfa<T> {
    pub fn dump_to_dot(&self) -> String {
        let mut s = String::from("digraph G {\n");

        for i in &self.accepting {
            s.push_str(format!("{i} [peripheries=2];\n").as_str())
        }

        for ((state_from, val), state_to) in &self.transitions {
            s.push_str(format!("{state_from} -> {state_to} [ label=\"{:?}\" ];\n", val).as_str());
        }

        s.push_str("}\n");
        s
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use regex::Regex;
    use std::fs::write;

    // Format
    //
    // <state>, <char> -> <state>
    // ... (n times)
    // <accepting state>
    // ... (m times)
    // <start state>
    pub fn parse_string(s: &str) -> Option<(Transtions<char>, State, Vec<State>)> {
        let lines = s.lines().collect::<Vec<_>>();
        let re = Regex::new(r"(\d), (.) -> (\d)").unwrap();
        let re1 = Regex::new(r"(\d)").unwrap();

        let mut trans = Transtions::<char>::new();
        let mut acc = Vec::new();

        for i in &lines[..lines.len() - 1] {
            if let Some(t) = re.captures(i) {
                trans.insert(
                    (t[1].parse().unwrap(), t[2].chars().next().unwrap()),
                    t[3].parse().unwrap(),
                );
            } else if let Some(a) = re1.captures(i) {
                acc.push(a[1].parse().unwrap());
            } else {
                return None;
            }
        }

        if let Some(start) = re1.captures(lines.last().unwrap()) {
            Some((trans, start[1].parse().unwrap(), acc))
        } else {
            None
        }
    }

    #[test]
    fn basic_dfa() {
        let s = "0, a -> 1\n1\n0";

        let dfa = parse_string(s).unwrap();
        let mut dfa = Dfa::new(dfa.0, dfa.1, dfa.2);

        assert!(dfa.run("a".chars().collect::<Vec<_>>().as_slice()));
        assert!(!dfa.run("abc".chars().collect::<Vec<_>>().as_slice()));
    }

    #[test]
    fn basic_dfa_1() {
        let s = "0, a -> 1\n1, b -> 2\n2\n0";

        let dfa = parse_string(s).unwrap();
        let mut dfa = Dfa::new(dfa.0, dfa.1, dfa.2);

        assert!(dfa.run("ab".chars().collect::<Vec<_>>().as_slice()));
        assert!(!dfa.run("abc".chars().collect::<Vec<_>>().as_slice()));
    }

    #[test]
    fn basic_dfa_2() {
        let s = "0, a -> 1\n0, b -> 2\n1, c -> 3\n2, d -> 3\n3\n0";

        let dfa = parse_string(s).unwrap();
        let mut dfa = Dfa::new(dfa.0, dfa.1, dfa.2);

        assert!(dfa.run("ac".chars().collect::<Vec<_>>().as_slice()));
        assert!(dfa.run("bd".chars().collect::<Vec<_>>().as_slice()));
        assert!(!dfa.run("ad".chars().collect::<Vec<_>>().as_slice()));
    }
}
