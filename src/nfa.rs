use crate::dfa;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::atomic::{AtomicUsize, Ordering};

pub type State = usize;
pub type Transtion = (State, Option<char>);
pub type Transtions = HashMap<Transtion, Vec<State>>;

#[derive(Clone, Debug)]
pub struct ThompsonNfa {
    transitions: Transtions,
    start: State,
    accepting: State,
}

static STATE_CNT: AtomicUsize = AtomicUsize::new(0);

impl ThompsonNfa {
    pub fn new_one_symbol(c: char) -> Self {
        let start = STATE_CNT.fetch_add(1, Ordering::Relaxed);
        let accepting = STATE_CNT.fetch_add(1, Ordering::Relaxed);

        Self {
            transitions: Transtions::from([((start, Some(c)), vec![accepting])]),
            start,
            accepting,
        }
    }

    fn next_state() -> State {
        STATE_CNT.fetch_add(1, Ordering::Relaxed)
    }

    fn add_new_transition(&mut self, trans: Transtion, to: State) {
        if let Some(s) = self.transitions.get_mut(&trans) {
            s.push(to);
        } else {
            self.transitions.insert(trans, vec![to]);
        }
    }

    fn add_new_transitions(&mut self, trans: Transtion, mut to: Vec<State>) {
        if let Some(s) = self.transitions.get_mut(&trans) {
            s.append(&mut to);
        } else {
            self.transitions.insert(trans, to);
        }
    }

    pub fn run(&mut self, input: &str) -> bool {
        let mut vd = VecDeque::new();

        vd.push_back((self.start, input));

        while let Some((state, input)) = vd.pop_front() {
            if input.len() == 0 {
                if self.accepting == state {
                    return true;
                }

                if let Some(next) = self.transitions.get(&(state, None)) {
                    for i in next {
                        vd.push_back((*i, input));
                    }
                }

                continue;
            }

            let next_char = input.chars().next().unwrap();

            if let Some(next) = self.transitions.get(&(state, Some(next_char))) {
                for i in next {
                    vd.push_back((*i, &input[1..]));
                }
            }

            if let Some(next) = self.transitions.get(&(state, None)) {
                for i in next {
                    vd.push_back((*i, input));
                }
            }
        }

        false
    }

    pub fn alternate(&mut self, other: Self) {
        let mut next_state = Self::next_state();
        let mut new = Self {
            transitions: Transtions::new(),
            start: usize::MAX,
            accepting: usize::MAX,
        };

        // Insert start state.
        new.transitions
            .insert((next_state, None), vec![self.start, other.start]);
        new.start = next_state;
        next_state = Self::next_state();

        // Connect all accepting states to new accepting state
        new.add_new_transition((self.accepting, None), next_state);
        new.add_new_transition((other.accepting, None), next_state);

        // Setup everything else
        new.accepting = next_state;
        new.transitions.extend(other.transitions);
        new.transitions.extend(self.transitions.clone());

        *self = new;
    }

    pub fn concatentation(&mut self, other: Self) {
        let mut new = Self {
            transitions: Transtions::new(),
            start: usize::MAX,
            accepting: usize::MAX,
        };

        // Connect all accepting states in self to middle state
        new.add_new_transitions((self.accepting, None), vec![other.start]);

        new.accepting = other.accepting;
        new.start = self.start;
        new.transitions.extend(other.transitions);
        new.transitions.extend(self.transitions.clone());

        *self = new;
    }

    pub fn closure(&mut self) {
        let mut m = State::MIN;

        // Find next state
        self.transitions.iter().for_each(|((cur, _), vec)| {
            m = m.max(*cur);
            m = m.max(*vec.iter().max().unwrap());
        });

        let new_start = m + 1;
        let new_acc = m + 2;

        // Connect accepting to start
        self.add_new_transitions((self.accepting, None), vec![self.start, new_acc]);

        // Insert new start state
        self.add_new_transition((new_start, None), self.start);
        self.start = new_start;

        self.add_new_transition((self.start, None), new_acc);
        self.accepting = new_acc;
    }

    pub fn subset_transition(&self) -> dfa::Dfa<char> {
        let e_closure = |trans: &Transtions, state: State| -> Option<Vec<State>> {
            trans.get(&(state, None)).cloned()
        };

        let delta = |trans: &Transtions, states: Vec<State>, c: char| -> Vec<State> {
            let mut res = Vec::new();

            for i in states {
                if let Some(t) = trans.get(&(i, Some(c))) {
                    res.extend(t);
                }
            }

            res
        };

        let q0 = e_closure(&self.transitions, self.start).unwrap();
        let mut q = q0.clone();
        let mut worklist = Vec::from([q0]);

        while let Some(q) = worklist.pop() {}

        todo!()
    }
}

#[cfg(test)]
#[allow(dead_code)]
impl ThompsonNfa {
    pub fn dump_to_dot(&self) -> String {
        let mut s = String::from("digraph G {\n");

        s.push_str(format!("{} [peripheries=3];\n", self.accepting).as_str());
        s.push_str(format!("{} [peripheries=2];\n", self.start).as_str());

        for ((state_from, val), state_to) in &self.transitions {
            for i in state_to {
                s.push_str(format!("{state_from} -> {i} [ label=\"{:?}\" ];\n", val).as_str());
            }
        }

        s.push_str("}\n");
        s
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn basic_nfa() {
        let mut dfa = ThompsonNfa::new_one_symbol('a');

        assert!(dfa.run("a"));
        assert!(!dfa.run("abc"));
    }

    #[test]
    fn basic_nfa_1() {
        let mut dfa = ThompsonNfa::new_one_symbol('a');
        let dfa2 = ThompsonNfa::new_one_symbol('b');

        dfa.concatentation(dfa2);

        assert!(dfa.run("ab"));
        assert!(!dfa.run("abc"));
    }

    #[test]
    fn basic_nfa_2() {
        let mut dfa = ThompsonNfa::new_one_symbol('a');
        let dfa2 = ThompsonNfa::new_one_symbol('b');
        let mut dfa3 = ThompsonNfa::new_one_symbol('c');
        let dfa4 = ThompsonNfa::new_one_symbol('d');

        dfa.alternate(dfa2);
        dfa3.alternate(dfa4);
        dfa.concatentation(dfa3);

        assert!(dfa.run("ac"));
        assert!(dfa.run("bd"));
    }

    #[test]
    fn basic_nfa_auto_alternation() {
        let mut dfa1 = ThompsonNfa::new_one_symbol('a');

        assert!(dfa1.run("a"));

        let mut dfa2 = ThompsonNfa::new_one_symbol('b');

        assert!(dfa2.run("b"));

        dfa2.alternate(dfa1);
        assert!(dfa2.run("a"));
        assert!(dfa2.run("b"));

        assert!(!dfa2.run("0"));
        assert!(!dfa2.run("ab"));
    }

    #[test]
    fn basic_nfa_auto_concatentaion() {
        let mut dfa1 = ThompsonNfa::new_one_symbol('a');

        assert!(dfa1.run("a"));

        let mut dfa2 = ThompsonNfa::new_one_symbol('b');

        assert!(dfa2.run("b"));

        dfa2.concatentation(dfa1);
        assert!(dfa2.run("ba"));
        assert!(!dfa2.run("ab"));
    }

    #[test]
    fn basic_nfa_auto_closure() {
        let mut dfa1 = ThompsonNfa::new_one_symbol('a');

        assert!(dfa1.run("a"));

        dfa1.closure();

        assert!(dfa1.run("aaa"));
        assert!(dfa1.run("aaaaaaa"));
        assert!(dfa1.run("aaaaaaaaaaaaaaaaaaaaaaaa"));
    }

    #[test]
    fn basic_nfa_auto_complex_closure() {
        let mut dfa = ThompsonNfa::new_one_symbol('a');
        let dfa2 = ThompsonNfa::new_one_symbol('b');

        dfa.alternate(dfa2);

        assert!(dfa.run("a"));
        assert!(dfa.run("b"));

        dfa.closure();

        assert!(dfa.run("aaa"));
        assert!(dfa.run("aaaaaaa"));
        assert!(dfa.run("aaaaaaaaaaaaaaaaaaaaaaaa"));
        assert!(dfa.run("aaaabbababababbabababab"));
        assert!(!dfa.run("acaaabbababababbabababab"));
    }
}
