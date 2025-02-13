use crate::nfa::*;
use crate::dfa::*;
use std::collections::VecDeque;

#[derive(Eq, PartialEq, Debug, Clone, Copy)]
enum Op {
    OpenPar,
    ClosePar,
    Alter,
    Closure,
    Concat,
}

fn op_to_str(op: &Op) -> &str {
    match op {
        Op::Alter => "|",
        Op::Concat => ".",
        Op::Closure => "*",
        _ => panic!("wtf {:?}", op),
    }
}

fn compare_ops(op1: &Op, op2: &Op) -> bool {
    fn op_to_prec(op: &Op) -> u8 {
        match *op {
            Op::Closure => 2,
            Op::Concat => 1,
            Op::Alter => 0,
            _ => panic!(),
        }
    }

    op_to_prec(op1) > op_to_prec(op2)
}

fn convert_to_prefix(s: &str) -> Option<String> {
    let mut stack = VecDeque::<Op>::new();
    let mut res = String::new();

    fn push_to_stack(vd: &mut VecDeque<Op>, op: Op) -> String {
        let mut s = String::new();

        if op == Op::OpenPar {
            vd.push_front(op);
            return String::new();
        } else if op == Op::ClosePar {
            let mut cnt = 0;
            let s = vd
                .iter()
                .take_while(|x| **x != Op::OpenPar)
                .map(|x| op_to_str(x))
                .fold(String::new(), |mut x, y| {
                    cnt += 1;
                    x.push_str(y);
                    x
                });

            vd.drain(..cnt);

            let v = vd.pop_front().unwrap();
            assert!(v == Op::OpenPar);

            return s;
        }

        while let Some(v) = vd.front() {
            if *v != Op::OpenPar {
                if op == *v || compare_ops(v, &op) {
                    s.push_str(op_to_str(&v));
                } else {
                    break;
                }
            } else {
                break;
            }

            vd.pop_front().unwrap();
        }

        vd.push_front(op);
        s
    }

    let chars = s.chars().collect::<Vec<_>>();

    for ii in 0..s.len() {
        let i = chars[ii];

        if i.is_alphabetic() {
            res.push(i);

            if ii != s.len() - 1 {
                if chars[ii + 1] != '|' && chars[ii + 1] != ')' && chars[ii + 1] != '*' {
                    res.push_str(push_to_stack(&mut stack, Op::Concat).as_str());
                }
            }
        } else {
            res.push_str(
                match i {
                    '(' => {
                        let mut s = String::new();

                        if ii != 0 && chars[ii - 1] != '|' && chars[ii - 1] != '(' {
                            s.push_str(push_to_stack(&mut stack, Op::Concat).as_str());
                        }

                        s.push_str(push_to_stack(&mut stack, Op::OpenPar).as_str());

                        s
                    }
                    ')' => {
                        let mut s = String::new();

                        s.push_str(push_to_stack(&mut stack, Op::ClosePar).as_str());

                        if ii != chars.len() - 1
                            && chars[ii + 1] != '*'
                            && chars[ii + 1] != '|'
                            && chars[ii + 1] != ')'
                        {
                            s.push_str(push_to_stack(&mut stack, Op::Concat).as_str());
                        }

                        s
                    }
                    '|' => push_to_stack(&mut stack, Op::Alter),
                    '*' => push_to_stack(&mut stack, Op::Closure),
                    _ => {
                        eprintln!("Unknown symbol {:?}", i);
                        return None;
                    }
                }
                .as_str(),
            )
        }
    }

    for i in stack.iter().map(|x| op_to_str(x)) {
        res.push_str(i);
    }

    Some(res)
}

pub fn postfix_to_nfa(s: &str) -> Option<ThompsonNfa> {
    let mut stack = VecDeque::new();

    for i in s.chars() {
        if i.is_alphabetic() {
            stack.push_front(ThompsonNfa::new_one_symbol(i));
        } else {
            match i {
                '.' => {
                    if stack.len() < 2 {
                        eprintln!("Wrong regex1");
                        return None;
                    }

                    let nfa1 = stack.pop_front().unwrap();
                    let mut nfa2 = stack.pop_front().unwrap();

                    nfa2.concatentation(nfa1);
                    stack.push_front(nfa2);
                }
                '|' => {
                    if stack.len() < 2 {
                        eprintln!("Wrong regex2");
                        return None;
                    }

                    let mut nfa1 = stack.pop_front().unwrap();
                    let nfa2 = stack.pop_front().unwrap();

                    nfa1.alternate(nfa2);
                    stack.push_front(nfa1);
                }
                '*' => {
                    if stack.len() < 1 {
                        eprintln!("Wrong regex3");
                        return None;
                    }

                    let mut nfa1 = stack.pop_front().unwrap();

                    nfa1.closure();
                    stack.push_front(nfa1);
                }
                _ => panic!(),
            }
        }
    }

    assert!(stack.len() == 1);
    stack.pop_front()
}

pub fn compile_regex(s: &str) -> Option<Dfa> {
    let s = convert_to_prefix(s)?;

    let nfa = postfix_to_nfa(s.as_str())?;
    Some(nfa.subset_transition())
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn basic_regex() {
        let mut r = compile_regex("a").unwrap();

        assert!(r.run("a"));
        assert!(!r.run("b"));
        assert!(!r.run("aa"));
    }

    #[test]
    fn basic_regex_alter() {
        let mut r = compile_regex("a|b").unwrap();

        assert!(r.run("a"));
        assert!(r.run("b"));
        assert!(!r.run("aa"));
        assert!(!r.run("ab"));
    }

    #[test]
    fn basic_regex_concat() {
        let mut r = compile_regex("ab").unwrap();

        assert!(!r.run("a"));
        assert!(!r.run("b"));
        assert!(!r.run("aa"));
        assert!(r.run("ab"));
        assert!(!r.run("abc"));
    }

    #[test]
    fn basic_regex_concat_and_alt() {
        let mut r = compile_regex("(a|b)c").unwrap();

        assert!(!r.run("aa"));
        assert!(!r.run("ab"));
        assert!(r.run("ac"));
        assert!(r.run("bc"));
        assert!(!r.run("bb"));
    }

    #[test]
    fn basic_regex_closure() {
        let mut r = compile_regex("a*").unwrap();

        assert!(r.run("aa"));
        assert!(r.run("aaaaa"));
        assert!(!r.run("aaaaab"));
        assert!(!r.run("aaaaabaaaaa"));
        assert!(!r.run("b"));
    }

    #[test]
    fn basic_regex_alter_closure() {
        let mut r = compile_regex("(a|b)*").unwrap();

        assert!(r.run("aaaaaaaa"));
        assert!(r.run("abababbabababbabab"));
        assert!(r.run("a"));
        assert!(r.run("b"));

        assert!(!r.run("c"));
        assert!(!r.run("aaaaabbcbb"));
        assert!(!r.run("aaaaabbbbc"));
    }

    #[test]
    fn basic_regex_alter_concat_closure() {
        let mut r = compile_regex("((a|b)c)*").unwrap();

        assert!(r.run("acac"));
        assert!(r.run("bcbc"));
        assert!(r.run("bcac"));
        assert!(r.run("acbc"));

        assert!(!r.run("cbac"));
        assert!(!r.run("ccbc"));
    }

    #[test]
    fn complex_regex() {
        let mut r = compile_regex("(a|b)c*(d|g)").unwrap();

        assert!(r.run("acd"));
        assert!(r.run("bcg"));
        assert!(r.run("bcccccg"));

        assert!(!r.run("gccd"));
    }

    #[test]
    fn basic_regex_long_word() {
        let mut r = compile_regex("(hello|world)").unwrap();

        assert!(r.run("hello"));
        assert!(r.run("world"));

        assert!(!r.run("sfsfsdfsdf"));
        assert!(!r.run("hel"));
    }

    #[test]
    fn complex_regex_long_word() {
        let mut r = compile_regex("(hello|world)*").unwrap();

        assert!(r.run("hello"));
        assert!(r.run("world"));
        assert!(r.run("worldhello"));
        assert!(r.run("worldhellohello"));

        assert!(!r.run("worldhelloheldlo"));

    }
}
