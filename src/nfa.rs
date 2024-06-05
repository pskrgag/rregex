use std::collections::HashMap;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::hash::Hash;

pub type State = usize;
pub type Transtion<T> = (State, Option<T>);
pub type Transtions<T> = HashMap<Transtion<T>, Vec<State>>;

#[derive(Clone, Debug)]
pub struct ThompsonNfa<T> {
    transitions: Transtions<T>,
    start: State,
    accepting: State,
}

impl<T: Eq + Hash + Copy + Debug> ThompsonNfa<T> {
    fn zip_nfas(&mut self, other: &mut Self) -> State {
        let mut transitions = Transtions::<T>::new();
        let mut state_num = 0;
        let mut other_mapping = HashMap::<State, State>::new();
        let mut self_mapping = HashMap::<State, State>::new();

        let mut map_state = |base: &mut HashMap<State, State>, st: State| -> State {
            if let Some(v) = base.get(&st) {
                *v
            } else {
                let s = state_num;
                base.insert(st, s);

                state_num += 1;
                s
            }
        };

        for ((state_from, val), state_to) in &other.transitions {
            transitions.insert(
                (map_state(&mut other_mapping, *state_from), *val),
                state_to
                    .iter()
                    .map(|x| map_state(&mut other_mapping, *x))
                    .collect(),
            );
        }

        other.transitions = transitions.clone();
        other.start = *other_mapping.get(&other.start).unwrap();
        other.accepting = *other_mapping.get(&other.accepting).unwrap();

        transitions.clear();

        for ((state_from, val), state_to) in &self.transitions {
            transitions.insert(
                (map_state(&mut self_mapping, *state_from), *val),
                state_to
                    .iter()
                    .map(|x| map_state(&mut self_mapping, *x))
                    .collect(),
            );
        }

        self.transitions = transitions;
        self.start = *self_mapping.get(&self.start).unwrap();
        self.accepting = *self_mapping.get(&self.accepting).unwrap();

        state_num
    }

    fn add_new_transition(&mut self, trans: Transtion<T>, to: State) {
        if let Some(s) = self.transitions.get_mut(&trans) {
            s.push(to);
        } else {
            self.transitions.insert(trans, vec![to]);
        }
    }

    fn add_new_transitions(&mut self, trans: Transtion<T>, mut to: Vec<State>) {
        if let Some(s) = self.transitions.get_mut(&trans) {
            s.append(&mut to);
        } else {
            self.transitions.insert(trans, to);
        }
    }

    pub fn new(transitions: Transtions<T>, start: State, accepting: State) -> Self {
        Self {
            transitions,
            start,
            accepting,
        }
    }

    pub fn run(&mut self, input: &[T]) -> bool {
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

            let next_char = input[0];

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

    pub fn alternate(&mut self, mut other: Self) {
        let mut next_state = self.zip_nfas(&mut other);
        let mut new = Self {
            transitions: Transtions::<T>::new(),
            start: usize::MAX,
            accepting: usize::MAX,
        };

        // Insert start state.
        new.transitions
            .insert((next_state, None), vec![self.start, other.start]);
        new.start = next_state;
        next_state += 1;

        // Connect all accepting states to new accepting state
        new.add_new_transition((self.accepting, None), next_state);
        new.add_new_transition((other.accepting, None), next_state);

        // Setup everything else
        new.accepting = next_state;
        new.transitions.extend(other.transitions);
        new.transitions.extend(self.transitions.clone());

        *self = new;
    }

    pub fn concatentation(&mut self, mut other: Self) {
        let mut new = Self {
            transitions: Transtions::<T>::new(),
            start: usize::MAX,
            accepting: usize::MAX,
        };

        self.zip_nfas(&mut other);

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
}

impl<T: Eq + Hash + Copy + Debug> ThompsonNfa<T> {
    pub fn dump_to_dot(&self) -> String {
        let mut s = String::from("digraph G {\n");

        s.push_str(format!("{} [peripheries=2];\n", self.accepting).as_str());

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
    use crate::helper::parse_string_nfa;

    #[test]
    fn basic_nfa() {
        let s = "0, a -> 1\n1\n0";

        let dfa = parse_string_nfa(s).unwrap();
        let mut dfa = ThompsonNfa::new(dfa.0, dfa.1, dfa.2);

        assert!(dfa.run("a".chars().collect::<Vec<_>>().as_slice()));
        assert!(!dfa.run("abc".chars().collect::<Vec<_>>().as_slice()));
    }

    #[test]
    fn basic_nfa_1() {
        let s = "0, a -> 1\n1, b -> 2\n2\n0";

        let dfa = parse_string_nfa(s).unwrap();
        let mut dfa = ThompsonNfa::new(dfa.0, dfa.1, dfa.2);

        assert!(dfa.run("ab".chars().collect::<Vec<_>>().as_slice()));
        assert!(!dfa.run("abc".chars().collect::<Vec<_>>().as_slice()));
    }

    #[test]
    fn basic_nfa_2() {
        let s = "0, a -> 1\n0, b -> 2\n1, c -> 3\n2, d -> 3\n3\n0";

        let dfa = parse_string_nfa(s).unwrap();
        let mut dfa = ThompsonNfa::new(dfa.0, dfa.1, dfa.2);

        assert!(dfa.run("ac".chars().collect::<Vec<_>>().as_slice()));
        assert!(dfa.run("bd".chars().collect::<Vec<_>>().as_slice()));
        assert!(!dfa.run("ad".chars().collect::<Vec<_>>().as_slice()));
    }

    #[test]
    fn basic_nfa_manual_alternation() {
        let s = "0, . -> 1\n0, . -> 2\n1, a -> 3\n2, b -> 4\n3, . -> 5\n4, . -> 5\n5\n0";

        let dfa = parse_string_nfa(s).unwrap();
        let mut dfa = ThompsonNfa::new(dfa.0, dfa.1, dfa.2);

        assert!(dfa.run("a".chars().collect::<Vec<_>>().as_slice()));
        assert!(dfa.run("b".chars().collect::<Vec<_>>().as_slice()));
        assert!(!dfa.run("ab".chars().collect::<Vec<_>>().as_slice()));
    }

    #[test]
    fn basic_nfa_auto_alternation() {
        let s = "0, a -> 1\n1\n0";
        let dfa = parse_string_nfa(s).unwrap();
        let mut dfa1 = ThompsonNfa::new(dfa.0, dfa.1, dfa.2);

        assert!(dfa1.run("a".chars().collect::<Vec<_>>().as_slice()));

        let s = "0, b -> 1\n1\n0";
        let dfa = parse_string_nfa(s).unwrap();
        let mut dfa2 = ThompsonNfa::new(dfa.0, dfa.1, dfa.2);

        assert!(dfa2.run("b".chars().collect::<Vec<_>>().as_slice()));

        dfa2.alternate(dfa1);
        assert!(dfa2.run("a".chars().collect::<Vec<_>>().as_slice()));
        assert!(dfa2.run("b".chars().collect::<Vec<_>>().as_slice()));

        assert!(!dfa2.run("0".chars().collect::<Vec<_>>().as_slice()));
        assert!(!dfa2.run("ab".chars().collect::<Vec<_>>().as_slice()));
    }

    #[test]
    fn basic_nfa_auto_concatentaion() {
        let s = "0, a -> 1\n1\n0";
        let dfa = parse_string_nfa(s).unwrap();
        let mut dfa1 = ThompsonNfa::new(dfa.0, dfa.1, dfa.2);

        assert!(dfa1.run("a".chars().collect::<Vec<_>>().as_slice()));

        let s = "0, b -> 1\n1\n0";
        let dfa = parse_string_nfa(s).unwrap();
        let mut dfa2 = ThompsonNfa::new(dfa.0, dfa.1, dfa.2);

        assert!(dfa2.run("b".chars().collect::<Vec<_>>().as_slice()));

        dfa2.concatentation(dfa1);
        assert!(dfa2.run("ba".chars().collect::<Vec<_>>().as_slice()));
        assert!(!dfa2.run("ab".chars().collect::<Vec<_>>().as_slice()));
    }

    #[test]
    fn basic_nfa_auto_closure() {
        let s = "0, a -> 1\n1\n0";
        let dfa = parse_string_nfa(s).unwrap();
        let mut dfa1 = ThompsonNfa::new(dfa.0, dfa.1, dfa.2);

        assert!(dfa1.run("a".chars().collect::<Vec<_>>().as_slice()));

        dfa1.closure();

        assert!(dfa1.run("aaa".chars().collect::<Vec<_>>().as_slice()));
        assert!(dfa1.run("aaaaaaa".chars().collect::<Vec<_>>().as_slice()));
        assert!(dfa1.run("aaaaaaaaaaaaaaaaaaaaaaaa".chars().collect::<Vec<_>>().as_slice()));
    }

    #[test]
    fn basic_nfa_auto_complex_closure() {
        let s = "0, . -> 1\n0, . -> 2\n1, a -> 3\n2, b -> 4\n3, . -> 5\n4, . -> 5\n5\n0";
        let dfa = parse_string_nfa(s).unwrap();
        let mut dfa = ThompsonNfa::new(dfa.0, dfa.1, dfa.2);

        assert!(dfa.run("a".chars().collect::<Vec<_>>().as_slice()));
        assert!(dfa.run("b".chars().collect::<Vec<_>>().as_slice()));

        dfa.closure();

        assert!(dfa.run("aaa".chars().collect::<Vec<_>>().as_slice()));
        assert!(dfa.run("aaaaaaa".chars().collect::<Vec<_>>().as_slice()));
        assert!(dfa.run("aaaaaaaaaaaaaaaaaaaaaaaa".chars().collect::<Vec<_>>().as_slice()));
        assert!(dfa.run("aaaabbababababbabababab".chars().collect::<Vec<_>>().as_slice()));
        assert!(!dfa.run("acaaabbababababbabababab".chars().collect::<Vec<_>>().as_slice()));
    }
}
