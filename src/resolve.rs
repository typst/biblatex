use std::collections::HashMap;
use std::mem::take;

use unicode_normalization::char;

use super::types::get_month_for_abbr;
use super::Chunk;

/// Fully parse a value, resolving abbreviations and LaTeX commands.
pub fn resolve(value: &str, abbreviations: &HashMap<&str, &str>) -> Vec<Chunk> {
    let parsed = parse_string(value);
    let resolved = resolve_abbreviations(parsed, abbreviations);
    let evaluated = resolve_latex_commands(resolved);
    evaluated
        .into_iter()
        .map(|raw| match raw {
            RawChunk::Normal(n) => Chunk::Normal(n),
            RawChunk::Verbatim(v) => Chunk::Verbatim(v),
            raw => panic!("raw chunk should have been resolved: {:?}", raw),
        })
        .collect()
}

/// A not yet fully resolved chunk.
#[derive(Debug, Clone, Eq, PartialEq)]
enum RawChunk {
    /// Normal values within quotes or single braces subject to
    /// capitalization formatting.
    Normal(String),
    /// Values nested in braces that are to be printed like specified
    /// in the file. Escapes keywords.
    ///
    /// Example: `"Inside {NASA}"` or `{Memes are {gReAT}}`.
    Verbatim(String),
    /// BibTeX allows strings to be saved and concatenated later.
    /// This chunk is a reference to a named string to be resolved.
    ///
    /// Example: `author1 # " and " # author2`
    Abbreviation(String),
    /// LaTeX command names within quotes or braces.
    /// May be followed by `Chunk::CommandArgs` in chunk slices.
    CommandName(String, bool),
    /// LaTeX command arguments.
    /// Must be preceeded by `Chunk::CommandName` in chunk slices.
    CommandArgs(String),
}

/// Create a chunk vector from field value string.
fn parse_string(value: &str) -> Vec<RawChunk> {
    /// Symbols that may occur while parsing a field value.
    #[derive(Debug, PartialEq)]
    enum Symbols {
        Quotes,
        Braces,
        Command,
    }

    #[derive(Debug, PartialEq)]
    enum EscCommandMode {
        /// Character escapes and TeX commands are possible.
        Both,
        /// Continuing a TeX command is possible.
        OnlyCommand,
        Neither,
    }

    let mut stack: Vec<Symbols> = vec![];
    let mut vals: Vec<RawChunk> = vec![];
    let mut allow_resolvable = true;
    let mut is_math = false;
    let mut expect_arg = false;
    let mut esc_cmd_mode = EscCommandMode::Neither;

    for c in value.chars().peekable() {
        if c == '$' && esc_cmd_mode != EscCommandMode::Both {
            is_math = !is_math;
        }

        match c {
            _ if esc_cmd_mode == EscCommandMode::Both && is_escapable(c) => {
                let _success = if let Some(x) = vals.last_mut() {
                    if let RawChunk::Normal(s) = x {
                        s.push(c);
                        true
                    } else if let RawChunk::Verbatim(s) = x {
                        s.push(c);
                        true
                    } else {
                        false
                    }
                } else {
                    false
                };

                // TODO: Report unexpected escape if !success
            }

            '{' if stack.last() != Some(&Symbols::Command) && !is_math => {
                allow_resolvable = false;
                stack.push(Symbols::Braces);
            }
            '{' if stack.last() == Some(&Symbols::Command) => {
                expect_arg = false;
            }
            '}' if stack.last() == Some(&Symbols::Command) => {
                assert_eq!(stack.pop(), Some(Symbols::Command));
            }
            '}' if !is_math => {
                assert_eq!(stack.pop(), Some(Symbols::Braces));
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
                vals.push(RawChunk::CommandArgs(c.to_string()));
                stack.pop();
                expect_arg = false;
            }

            _ if esc_cmd_mode != EscCommandMode::Neither && !c.is_whitespace() => {
                match vals.last_mut() {
                    Some(RawChunk::CommandName(s, _))
                        if esc_cmd_mode == EscCommandMode::OnlyCommand =>
                    {
                        s.push(c);
                    }
                    _ => {
                        esc_cmd_mode = EscCommandMode::OnlyCommand;
                        vals.push(RawChunk::CommandName(c.to_string(), stack.len() > 1));
                        if !matches!(stack.last(), Some(Symbols::Command)) {
                            stack.push(Symbols::Command);
                        }
                        if is_single_char_func(c) {
                            esc_cmd_mode = EscCommandMode::Neither;
                            expect_arg = true;
                        }
                    }
                };

                continue;
            }

            _ if stack.last() == Some(&Symbols::Command) => match vals.last_mut() {
                Some(RawChunk::CommandArgs(s)) => s.push(c),
                _ => vals.push(RawChunk::CommandArgs(c.to_string())),
            },

            _ if stack.is_empty() => match vals.last_mut() {
                Some(RawChunk::Abbreviation(s)) if !allow_resolvable => s.push(c),
                _ if allow_resolvable => {
                    allow_resolvable = false;
                    vals.push(RawChunk::Abbreviation(c.to_string()))
                }
                _ => {}
            },

            '~' if !stack.is_empty() => match vals.last_mut() {
                Some(RawChunk::Normal(s)) => s.push('\u{00A0}'),
                Some(RawChunk::Verbatim(s)) => s.push('\u{00A0}'),
                _ if stack.len() == 1 => {
                    vals.push(RawChunk::Normal('\u{00A0}'.to_string()));
                }
                _ => {
                    vals.push(RawChunk::Verbatim('\u{00A0}'.to_string()));
                }
            },

            _ if stack.len() == 1 => match vals.last_mut() {
                Some(RawChunk::Normal(s)) => s.push(c),
                _ => vals.push(RawChunk::Normal(c.to_string())),
            },

            _ => match vals.last_mut() {
                Some(RawChunk::Verbatim(s)) => s.push(c),
                _ => vals.push(RawChunk::Verbatim(c.to_string())),
            },
        }

        esc_cmd_mode = EscCommandMode::Neither;
    }

    vals
}

/// Resolves `Chunk::Abbreviation` items to their respective string values.
fn resolve_abbreviations(s: Vec<RawChunk>, map: &HashMap<&str, &str>) -> Vec<RawChunk> {
    let mut res: Vec<RawChunk> = vec![];

    for elem in s.into_iter() {
        if let RawChunk::Abbreviation(x) = elem {
            // FIXME: Prevent cyclic evaluation.
            let val = map
                .get(x.as_str())
                .map(|&s| resolve_abbreviations(parse_string(s), map));

            if let Some(mut x) = val {
                res.append(&mut x);
            } else if let Some(x) = get_month_for_abbr(&x) {
                res.push(RawChunk::Normal(x.0));
            }
        } else {
            res.push(elem);
        }
    }

    flatten(res)
}

/// Best-effort evaluation of LaTeX commands with a focus on diacritics.
/// Will dump the command arguments if evaluation not possible.
/// Nested commands are not supported.
fn resolve_latex_commands(values: Vec<RawChunk>) -> Vec<RawChunk> {
    use std::iter::Peekable;
    use std::vec::IntoIter;

    let mut res: Vec<RawChunk> = vec![];

    let mut iter = values.into_iter().peekable();

    fn modify_args(
        iter: &mut Peekable<IntoIter<RawChunk>>,
        verb: bool,
        f: impl Fn(String) -> String,
    ) -> Option<RawChunk> {
        // Don't treat commands as arguments.
        if let Some(&RawChunk::CommandName(..)) = iter.peek() {
            None
        } else {
            match iter.next() {
                Some(RawChunk::CommandArgs(args)) => Some(to_value(&f(args), verb)),
                chunk => chunk,
            }
        }
    }

    fn last_char_combine(mut v: String, combine: char) -> String {
        if let Some(c) = v.pop().and_then(|c| char::compose(c, combine)) {
            v.push(c);
        }
        v
    }

    fn to_value(s: &str, verb: bool) -> RawChunk {
        if verb {
            RawChunk::Verbatim(s.to_string())
        } else {
            RawChunk::Normal(s.to_string())
        }
    }

    while let Some(val) = iter.next() {
        let (cmd, verb) = match val {
            RawChunk::CommandName(cmd, verb) => (cmd, verb),
            RawChunk::CommandArgs(_) => {
                panic!("command args where not preceded by command name")
            }
            chunk => {
                res.push(chunk);
                continue;
            }
        };

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
            "o" if !matches!(iter.peek(), Some(RawChunk::CommandArgs(_))) => {
                Some(to_value("ø", verb))
            }
            "O" => Some(to_value("Ø", verb)),
            "ss" => Some(to_value("ß", verb)),
            "SS" => Some(to_value("ẞ", verb)),
            "`" => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{300}')),
            "´" => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{301}')),
            "'" => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{301}')),
            "^" => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{302}')),
            "~" => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{303}')),
            "=" => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{304}')),
            "u" => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{306}')),
            "." => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{307}')),
            "\"" => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{308}')),
            "r" => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{30A}')),
            "H" => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{30B}')),
            "v" => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{30C}')),
            "d" => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{323}')),
            "c" => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{327}')),
            "k" => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{328}')),
            "b" => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{332}')),
            "o" => modify_args(&mut iter, verb, |v| last_char_combine(v, '\u{338}')),
            "t" => modify_args(&mut iter, verb, |mut v| {
                // FIXME: This one does not seem to work.
                let last = v.pop();
                v.push('\u{361}');
                if let Some(c) = last {
                    v.push(c);
                }
                v
            }),
            _ => modify_args(&mut iter, verb, |v| v),
        };

        if let Some(v) = next {
            res.push(v)
        }
    }

    flatten(res)
}

/// Simplifies a chunk vector by collapsing neighboring Normal or Verbatim chunks.
fn flatten(s: Vec<RawChunk>) -> Vec<RawChunk> {
    let mut normal = String::new();
    let mut verbatim = String::new();
    let mut res: Vec<RawChunk> = vec![];

    for elem in s {
        if let RawChunk::Normal(x) = elem {
            if !verbatim.is_empty() {
                res.push(RawChunk::Verbatim(take(&mut verbatim)));
            }
            normal += &x;
        } else if let RawChunk::Verbatim(x) = elem {
            if !normal.is_empty() {
                res.push(RawChunk::Normal(take(&mut normal)));
            }
            verbatim += &x;
        } else {
            if !verbatim.is_empty() {
                res.push(RawChunk::Verbatim(take(&mut verbatim)));
            }

            if !normal.is_empty() {
                res.push(RawChunk::Normal(take(&mut normal)));
            }

            res.push(elem);
        }
    }

    if !verbatim.is_empty() {
        res.push(RawChunk::Verbatim(verbatim));
    }

    if !normal.is_empty() {
        res.push(RawChunk::Normal(normal));
    }

    res
}

/// Characters that can be escaped.
pub fn is_escapable(c: char) -> bool {
    match c {
        '&' | '%' | '{' | '}' | '$' | '_' => true,
        _ => false,
    }
}

/// Characters that are the name of a single-char command
/// that automatically terminates.
fn is_single_char_func(c: char) -> bool {
    match c {
        '"' | '´' | '`' | '\'' | '^' | '~' | '=' | '.' => true,
        _ => false,
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
#[rustfmt::skip]
mod tests {
    use std::collections::HashMap;

    use super::{resolve_latex_commands, parse_string, resolve_abbreviations, RawChunk};

    fn R(s: &str) -> RawChunk {
        RawChunk::Abbreviation(s.to_string())
    }
    fn N(s: &str) -> RawChunk {
        RawChunk::Normal(s.to_string())
    }
    fn V(s: &str) -> RawChunk {
        RawChunk::Verbatim(s.to_string())
    }
    fn C(s: &str, verb: bool) -> RawChunk {
        RawChunk::CommandName(s.to_string(), verb)
    }
    fn CA(s: &str) -> RawChunk {
        RawChunk::CommandArgs(s.to_string())
    }

    #[test]
    fn test_process() {
        let res = parse_string("abc # \"good {TIMES}\" # hi # you # \"last\"");
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
        let res = parse_string("\"\\\"{A}ther und {\"\\LaTeX \"} {\\relax for you\\}}\"");
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

        let res = parse_string("\"M\\\"etal S\\= ound\"");
        assert_eq!(res[0], N("M"));
        assert_eq!(res[1], C("\"", false));
        assert_eq!(res[2], CA("e"));
        assert_eq!(res[3], N("tal S"));
        assert_eq!(res[4], C("=", false));
        assert_eq!(res[5], CA("o"));
        assert_eq!(res[6], N("und"));
    }

    #[test]
    fn test_resolve_strings() {
        let res = parse_string("a # b # c # \" \\\"{a} and others\"");
        let mut map = HashMap::new();
        map.insert("a", "\"trees\"");
        map.insert("b", "\"bushes\"");
        map.insert("c", "a # \" and \" # b");

        let res = resolve_abbreviations(res, &map);
        assert_eq!(res[0], N("treesbushestrees and bushes "));
        assert_eq!(res[1], C("\"", false));
        assert_eq!(res[2], CA("a"));
        assert_eq!(res[3], N(" and others"));

        let map = HashMap::new();
        let res = resolve_abbreviations(parse_string("Jan # \"~12\""), &map);
        assert_eq!(res[0], N("January\u{A0}12"));
    }

    #[test]
    fn test_math() {
        let res = parse_string("{The $11^{th}$ International Conference on How To Make \\$\\$}");
        assert_eq!(res[0], N("The $11^{th}$ International Conference on How To Make $$"));
        assert_eq!(res.len(), 1);
    }

    #[test]
    fn test_commands() {
        let res = resolve_latex_commands(parse_string("{\\LaTeX{}~is gr\\~e\\`at\\o \\t{oo}"));
        assert_eq!(res[0], V("LaTeX"));
        assert_eq!(res[1], N("\u{00A0}is grẽàtøo\u{361}o"));
    }
}
