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
    use std::fs::write;
    use crate::helper::parse_string;

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
