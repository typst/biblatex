use std::collections::HashMap;
use std::mem::take;
use unicode_normalization::char;

use crate::syntax::BiblatexParser;

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Verbatim(String),
    Normal(String),
    Resolve(String),
    CommandName(String, bool),
    CommandArgs(String),
}

#[derive(Debug, PartialEq)]
pub enum Symbols {
    Quotes,
    Braces,
    Command,
}

#[derive(Clone, Debug, Default)]
pub struct CollectionEntry<'s> {
    pub entry_type: &'s str,
    pub props: HashMap<&'s str, Vec<Value>>,
}

pub fn new_collection<'s>(
    src: &'s str,
    allow_bibtex: bool,
) -> Vec<(&'s str, CollectionEntry)> {
    let parsed = BiblatexParser::new(src, allow_bibtex).parse();
    let mut coll_vec = vec![];

    for e in parsed.entries.into_iter() {
        let cite_key = e.0;
        let mut collection_entry = CollectionEntry {
            entry_type: e.1.entry_type,
            props: HashMap::new(),
        };
        for prop in e.1.props {
            collection_entry.props.insert(
                prop.0,
                eval_latex_commands(resolve(process_string(prop.1), &parsed.strings)),
            );
        }
        coll_vec.push((cite_key, collection_entry));
    }

    coll_vec
}

fn process_string(s: &str) -> Vec<Value> {
    let mut iter = s.chars().peekable();
    let mut stack: Vec<Symbols> = vec![];
    let mut vals: Vec<Value> = vec![];
    let mut allow_resolvable = true;
    let mut is_math = false;
    let mut expect_arg = false;

    #[derive(Debug, PartialEq)]
    enum EscCommandMode {
        Both,
        OnlyCommand,
        Neither,
    }
    let mut esc_cmd_mode = EscCommandMode::Neither;

    for c in iter {
        if c == '$' && esc_cmd_mode != EscCommandMode::Both {
            is_math = !is_math;
        }

        match c {
            _ if esc_cmd_mode == EscCommandMode::Both && is_escapable(c) => {
                let _success = if let Some(x) = vals.last_mut() {
                    if let Value::Normal(s) = x {
                        s.push(c);
                        true
                    } else if let Value::Verbatim(s) = x {
                        s.push(c);
                        true
                    } else {
                        false
                    }
                } else {
                    false
                };

                // TODO report unexpected escape if !success
            }
            '{' if stack.last() != Some(&Symbols::Command) && !is_math => {
                allow_resolvable = false;
                stack.push(Symbols::Braces);
            }
            '{' if stack.last() == Some(&Symbols::Command) => {
                expect_arg = false;
            }
            '}' if stack.last() == Some(&Symbols::Command) => {
                let x = stack.pop();
                assert_eq!(x, Some(Symbols::Command));
            }
            '}' if !is_math => {
                let x = stack.pop();
                assert_eq!(x, Some(Symbols::Braces));
            }
            '"' if stack.is_empty() => {
                allow_resolvable = false;
                stack.push(Symbols::Quotes);
            }
            '"' if stack.len() == 1
                && stack.last() == Some(&Symbols::Quotes)
                && esc_cmd_mode != EscCommandMode::Both =>
            {
                stack.pop();
            }
            '#' if stack.is_empty() => {
                allow_resolvable = true;
            }
            '\\' if esc_cmd_mode != EscCommandMode::Both => {
                esc_cmd_mode = EscCommandMode::Both;
                continue;
            }
            _ if (stack.is_empty() || expect_arg) && c.is_whitespace() => {}
            _ if c.is_whitespace() && stack.last() == Some(&Symbols::Command) => {
                stack.pop();
            }
            _ if c.is_whitespace() && esc_cmd_mode == EscCommandMode::OnlyCommand => {}
            '\n' => {}
            '\r' => {}
            _ if expect_arg => {
                vals.push(Value::CommandArgs(c.to_string()));
                stack.pop();
                expect_arg = false;
            }
            _ if esc_cmd_mode != EscCommandMode::Neither && !c.is_whitespace() => {
                let success = if esc_cmd_mode != EscCommandMode::Both {
                    if let Some(x) = vals.last_mut() {
                        if let Value::CommandName(s, _) = x {
                            s.push(c);
                            true
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                };

                esc_cmd_mode = EscCommandMode::OnlyCommand;
                if !success {
                    vals.push(Value::CommandName(c.to_string(), stack.len() > 1));
                    stack.push(Symbols::Command);
                    if is_single_char_func(c) {
                        esc_cmd_mode = EscCommandMode::Neither;
                        expect_arg = true;
                    }
                }
                continue;
            }
            _ if stack.last() == Some(&Symbols::Command) => {
                let success = if let Some(x) = vals.last_mut() {
                    if let Value::CommandArgs(s) = x {
                        s.push(c);
                        true
                    } else {
                        false
                    }
                } else {
                    false
                };

                if !success {
                    vals.push(Value::CommandArgs(c.to_string()))
                }
            }
            _ if stack.is_empty() => {
                let success = if !allow_resolvable {
                    if let Some(x) = vals.last_mut() {
                        if let Value::Resolve(s) = x {
                            s.push(c);
                            true
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                };

                if !success && allow_resolvable {
                    allow_resolvable = false;
                    vals.push(Value::Resolve(c.to_string()))
                }
            }
            _ if stack.len() == 1 => {
                let success = if let Some(x) = vals.last_mut() {
                    if let Value::Normal(s) = x {
                        s.push(c);
                        true
                    } else {
                        false
                    }
                } else {
                    false
                };

                if !success {
                    vals.push(Value::Normal(c.to_string()))
                }
            }
            _ if stack.len() > 1 => {
                let success = if let Some(x) = vals.last_mut() {
                    if let Value::Verbatim(s) = x {
                        s.push(c);
                        true
                    } else {
                        false
                    }
                } else {
                    false
                };

                if !success {
                    vals.push(Value::Verbatim(c.to_string()))
                }
            }
            _ => unreachable!(),
        }
        esc_cmd_mode = EscCommandMode::Neither;
    }

    vals
}

fn resolve(s: Vec<Value>, map: &HashMap<&str, &str>) -> Vec<Value> {
    let mut res: Vec<Value> = vec![];

    for elem in s.into_iter() {
        if let Value::Resolve(x) = elem {
            let val = map.get(x.as_str()).map(|&s| resolve(process_string(s), map));

            if let Some(mut x) = val {
                res.append(&mut x);
            }
        } else {
            res.push(elem);
        }
    }

    flatten(res)
}

fn flatten(s: Vec<Value>) -> Vec<Value> {
    let mut normal = String::new();
    let mut verbatim = String::new();
    let mut res: Vec<Value> = vec![];

    for elem in s.into_iter() {
        if let Value::Normal(x) = elem {
            if !verbatim.is_empty() {
                res.push(Value::Verbatim(take(&mut verbatim)));
            }
            normal += &x;
        } else if let Value::Verbatim(x) = elem {
            if !normal.is_empty() {
                res.push(Value::Normal(take(&mut normal)));
            }
            verbatim += &x;
        } else {
            if !verbatim.is_empty() {
                res.push(Value::Verbatim(take(&mut verbatim)));
            }

            if !normal.is_empty() {
                res.push(Value::Normal(take(&mut normal)));
            }

            res.push(elem);
        }
    }

    if !verbatim.is_empty() {
        res.push(Value::Verbatim(verbatim));
    }

    if !normal.is_empty() {
        res.push(Value::Normal(normal));
    }

    res
}

fn eval_latex_commands(values: Vec<Value>) -> Vec<Value> {
    let mut res: Vec<Value> = vec![];
    let mut iter = values.into_iter().peekable();

    fn modify_args(
        val: Option<Value>,
        verb: bool,
        f: impl Fn(String) -> String,
    ) -> Option<Value> {
        val.map(|val| {
            if let Value::CommandArgs(args) = val {
                to_value(&f(args), verb)
            } else {
                val
            }
        })
    }

    fn last_char_combine(mut v: String, combine: char) -> String {
        let l = v.pop().and_then(|c| char::compose(c, combine));
        if let Some(c) = l {
            v.push(c);
        }

        v
    }

    fn to_value(s: &str, verb: bool) -> Value {
        if verb {
            Value::Verbatim(s.to_string())
        } else {
            Value::Normal(s.to_string())
        }
    }

    while let Some(val) = iter.next() {
        if let Value::CommandName(cmd, verb) = val {
            let next = match cmd.as_str() {
                "LaTeX" => Some(to_value("LaTeX", true)),
                "TeX" => Some(to_value("TeX", true)),
                "aa" => Some(to_value("å", verb)),
                "AA" => Some(to_value("Å", verb)),
                "l" => Some(to_value("ł", verb)),
                "L" => Some(to_value("Ł", verb)),
                "i" => Some(to_value("ı", verb)),
                "oe" => Some(to_value("œ", verb)),
                "OE" => Some(to_value("Œ", verb)),
                "ae" => Some(to_value("æ", verb)),
                "AE" => Some(to_value("Æ", verb)),
                "o" if !matches!(iter.peek(), Some(Value::CommandArgs(_))) => {
                    Some(to_value("ø", verb))
                }
                "O" => Some(to_value("Ø", verb)),
                "ss" => Some(to_value("ß", verb)),
                "SS" => Some(to_value("ẞ", verb)),
                "`" => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{300}'))
                }
                "´" => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{301}'))
                }
                "'" => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{301}'))
                }
                "^" => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{302}'))
                }
                "~" => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{303}'))
                }
                "=" => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{304}'))
                }
                "u" => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{306}'))
                }
                "." => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{307}'))
                }
                "\"" => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{308}'))
                }
                "r" => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{30A}'))
                }
                "H" => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{30B}'))
                }
                "v" => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{30C}'))
                }
                "d" => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{323}'))
                }
                "c" => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{327}'))
                }
                "k" => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{328}'))
                }
                "b" => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{332}'))
                }
                "o" => {
                    modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{338}'))
                }
                "t" => modify_args(iter.next(), verb, |mut v| {
                    // This one does not seem to work
                    let last = v.pop();
                    v.push('\u{361}');
                    if let Some(c) = last {
                        v.push(c);
                    }
                    v
                }),
                _ => modify_args(iter.next(), true, |v| v),
            };

            if let Some(v) = next {
                res.push(v)
            }
        } else {
            res.push(val);
        }
    }

    flatten(res)
}

fn is_escapable(c: char) -> bool {
    let escapable = "&%{},$'";
    escapable.contains(c)
}

fn is_single_char_func(c: char) -> bool {
    let escapable = "\"´`^~=.";
    escapable.contains(c)
}

#[cfg(test)]
mod tests {
    use super::{eval_latex_commands, process_string, resolve, Value};
    use std::collections::HashMap;

    fn R(s: &str) -> Value {
        Value::Resolve(s.to_string())
    }

    fn N(s: &str) -> Value {
        Value::Normal(s.to_string())
    }

    fn V(s: &str) -> Value {
        Value::Verbatim(s.to_string())
    }

    fn C(s: &str, verb: bool) -> Value {
        Value::CommandName(s.to_string(), verb)
    }

    fn CA(s: &str) -> Value {
        Value::CommandArgs(s.to_string())
    }

    #[test]
    fn test_process() {
        let res = process_string("abc # \"good {TIMES}\" # hi # you # \"last\"");
        assert_eq!(res[0], R("abc"));
        assert_eq!(res[1], N("good "));
        assert_eq!(res[2], V("TIMES"));
        assert_eq!(res[3], R("hi"));
        assert_eq!(res[4], R("you"));
        assert_eq!(res[5], N("last"));
        assert_eq!(res.len(), 6);
    }

    #[test]
    fn test_resolve_commands_and_escape() {
        let res =
            process_string("\"\\\"{A}ther und {\"\\LaTeX \"} {\\relax for you\\}}\"");
        assert_eq!(res[0], C("\"", false));
        assert_eq!(res[1], CA("A"));
        assert_eq!(res[2], N("ther und "));
        assert_eq!(res[3], V("\""));
        assert_eq!(res[4], C("LaTeX", true));
        assert_eq!(res[5], V("\""));
        assert_eq!(res[6], N(" "));
        assert_eq!(res[7], C("relax", true));
        assert_eq!(res[8], V("for you}"));
        assert_eq!(res.len(), 9);

        let res = process_string("\"M\\\"etal S\\= ound\"");
        assert_eq!(res[0], N("M"));
        assert_eq!(res[1], C("\"", false));
        assert_eq!(res[2], CA("e"));
        assert_eq!(res[3], N("tal S"));
        assert_eq!(res[4], C("=", false));
        assert_eq!(res[5], CA("o"));
        assert_eq!(res[6], N("und"));
    }

    #[test]
    fn test_math() {
        let res = process_string(
            "{The $11^{th}$ International Conference on How To Make \\$\\$}",
        );
        assert_eq!(
            res[0],
            N("The $11^{th}$ International Conference on How To Make $$")
        );
        assert_eq!(res.len(), 1);
    }

    #[test]
    fn test_resolve() {
        let res = process_string("a # b # c # \" \\\"{a} and others\"");
        let mut map = HashMap::new();
        map.insert("a", "\"trees\"");
        map.insert("b", "\"bushes\"");
        map.insert("c", "a # \" and \" # b");

        let res = resolve(res, &map);
        assert_eq!(res[0], N("treesbushestrees and bushes "));
        assert_eq!(res[1], C("\"", false));
        assert_eq!(res[2], CA("a"));
        assert_eq!(res[3], N(" and others"));
    }

    #[test]
    fn test_commands() {
        let res =
            eval_latex_commands(process_string("{\\LaTeX{} is gre\\`at\\o \\t{oo}"));
        assert_eq!(res[0], V("LaTeX"));
        assert_eq!(res[1], N(" is greàtøo\u{361}o"));
    }
}
