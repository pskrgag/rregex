use crate::dfa;
use crate::nfa;
use regex::Regex;

// Format
//
// <state>, <char> -> <state>
// ... (n times)
// <accepting state>
// ... (m times)
// <start state>
pub fn parse_string(s: &str) -> Option<(dfa::Transtions<char>, dfa::State, Vec<dfa::State>)> {
    let lines = s.lines().collect::<Vec<_>>();
    let re = Regex::new(r"(\d), (.) -> (\d)").unwrap();
    let re1 = Regex::new(r"(\d)").unwrap();

    let mut trans = dfa::Transtions::<char>::new();
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

pub fn parse_string_nfa(s: &str) -> Option<(nfa::Transtions<char>, nfa::State, Vec<nfa::State>)> {
    let lines = s.lines().collect::<Vec<_>>();
    let re = Regex::new(r"(\d), (.|\.) -> (\d)").unwrap();
    let re1 = Regex::new(r"(\d)").unwrap();

    let mut trans = nfa::Transtions::<char>::new();
    let mut acc = Vec::new();

    for i in &lines[..lines.len() - 1] {
        if let Some(t) = re.captures(i) {
            let next_c = &t[2];

            let next = if next_c == "." {
                None
            } else {
                Some(t[2].chars().next().unwrap())
            };

            if let Some(v) = trans.get_mut(&(t[1].parse().unwrap(), next)) {
                v.push(t[3].parse().unwrap());
            } else {
                trans.insert((t[1].parse().unwrap(), next), vec![t[3].parse().unwrap()]);
            }
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
