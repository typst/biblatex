use std::collections::HashMap;
use std::mem::take;

use unicode_normalization::char;

use crate::chunk::{Chunk, Chunks};
use crate::types::get_month_for_abbr;

/// Fully parse a value, resolving abbreviations and LaTeX commands.
pub fn resolve(value: &str, abbreviations: &HashMap<&str, &str>) -> Option<Chunks> {
    let parsed = parse_string(value, false)?.0;
    let resolved = resolve_abbreviations(parsed, abbreviations);
    let evaluated = resolve_latex_commands(resolved);
    Some(
        evaluated
            .into_iter()
            .map(|raw| match raw {
                RawChunk::Normal(n) => Chunk::Normal(n),
                RawChunk::PreserveCase(v) => Chunk::Verbatim(v),
                raw => panic!("raw chunk should have been resolved: {:?}", raw),
            })
            .collect(),
    )
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
    PreserveCase(String),
    /// BibTeX allows strings to be saved and concatenated later.
    /// This chunk is a reference to a named string to be resolved.
    ///
    /// Example: `author1 # " and " # author2`
    Abbreviation(String),
    /// LaTeX command names within quotes or braces.
    /// May be followed by `Chunk::CommandArgs` in chunk slices.
    /// The boolean indicates if the command has appeared in a
    /// verbatim context.
    /// Arguments may appear in the `Option<Vec<RawChunk>>` element.
    CommandName(String, bool, Option<Vec<RawChunk>>),
}

impl RawChunk {
    fn to_preserved(self) -> Self {
        if let Self::Normal(s) = self {
            Self::PreserveCase(s)
        } else {
            self
        }
    }

    fn display_string(&self) -> Option<&str> {
        match self {
            Self::Normal(s) => Some(s.as_ref()),
            Self::PreserveCase(s) => Some(s.as_ref()),
            _ => None,
        }
    }

    fn reset_string(self, s: String) -> Self {
        match self {
            Self::Normal(_) => Self::Normal(s),
            Self::PreserveCase(_) => Self::PreserveCase(s),
            Self::Abbreviation(_) => Self::Abbreviation(s),
            Self::CommandName(_, a, b) => Self::CommandName(s, a, b),
        }
    }
}

/// Create a chunk vector from field value string.
/// Recurses to resolve nested commands.
fn parse_string(
    value: &str,
    allow_stack_depletion: bool,
) -> Option<(Vec<RawChunk>, usize)> {
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

    let mut stack: Vec<Symbols> = if allow_stack_depletion {
        vec![Symbols::Braces]
    } else {
        vec![]
    };
    let mut vals: Vec<RawChunk> = vec![];
    let mut allow_resolvable = true;
    let mut is_math = false;
    let mut expect_arg = false;
    let mut esc_cmd_mode = EscCommandMode::Neither;
    let mut chars_iter = value.chars().enumerate().peekable();

    while let Some((index, c)) = chars_iter.next() {
        if c == '$' && esc_cmd_mode != EscCommandMode::Both {
            is_math = !is_math;
        }

        match c {
            _ if esc_cmd_mode == EscCommandMode::Both && is_escapable(c) => {
                if let Some(x) = vals.last_mut() {
                    if let RawChunk::Normal(s) = x {
                        s.push(c);
                    } else if let RawChunk::PreserveCase(s) = x {
                        s.push(c);
                    } else {
                        vals.push(RawChunk::Normal(c.into()));
                    }
                } else if stack.len() == 1 {
                    vals.push(RawChunk::Normal(c.into()));
                } else {
                    vals.push(RawChunk::PreserveCase(c.into()));
                }
            }

            '{' if stack.last() != Some(&Symbols::Command) && !is_math => {
                allow_resolvable = false;
                stack.push(Symbols::Braces);
            }
            '{' if stack.last() == Some(&Symbols::Command) => {
                let res = parse_string(&value[index + 1 ..], true)?;
                for _ in 0 .. (res.1 + 1) {
                    chars_iter.next();
                }

                if let Some(RawChunk::CommandName(_, _, args)) = vals.last_mut() {
                    args.replace(res.0);
                } else {
                    panic!(
                        "If the last symbol was a command, the stack has to have a Command."
                    );
                }

                stack.pop();

                expect_arg = false;
            }
            '}' if stack.last() == Some(&Symbols::Command) => {
                if stack.pop() != Some(Symbols::Command) {
                    return None;
                }
                if stack.pop() != Some(Symbols::Braces) {
                    return None;
                }
            }
            '}' if !is_math => {
                if stack.pop() != Some(Symbols::Braces) {
                    return None;
                }

                if stack.is_empty() && allow_stack_depletion {
                    return Some((vals, index));
                }
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

            _ if c.is_numeric() => match vals.last_mut() {
                Some(RawChunk::Normal(s)) => s.push(c),
                _ => vals.push(RawChunk::Normal(c.to_string())),
            },

            _ if expect_arg => {
                if let Some(RawChunk::CommandName(_, _, args)) = vals.last_mut() {
                    args.replace(vec![RawChunk::Normal(c.to_string())]);
                } else {
                    panic!(
                        "If an argument is expected, the stack has to have a Command."
                    );
                }
                stack.pop();
                expect_arg = false;
            }

            _ if esc_cmd_mode != EscCommandMode::Neither && !c.is_whitespace() => {
                match vals.last_mut() {
                    Some(RawChunk::CommandName(s, _, _))
                        if esc_cmd_mode == EscCommandMode::OnlyCommand =>
                    {
                        s.push(c);
                    }
                    _ => {
                        esc_cmd_mode = EscCommandMode::OnlyCommand;
                        vals.push(RawChunk::CommandName(
                            c.to_string(),
                            stack.len() > 1,
                            None,
                        ));
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
                Some(RawChunk::PreserveCase(s)) => s.push('\u{00A0}'),
                _ if stack.len() == 1 => {
                    vals.push(RawChunk::Normal('\u{00A0}'.to_string()));
                }
                _ => {
                    vals.push(RawChunk::PreserveCase('\u{00A0}'.to_string()));
                }
            },

            _ if stack.len() == 1 => match vals.last_mut() {
                Some(RawChunk::Normal(s)) => s.push(c),
                _ => vals.push(RawChunk::Normal(c.to_string())),
            },

            _ => match vals.last_mut() {
                Some(RawChunk::PreserveCase(s)) => s.push(c),
                _ => vals.push(RawChunk::PreserveCase(c.to_string())),
            },
        }

        esc_cmd_mode = EscCommandMode::Neither;
    }

    Some((vals, value.len()))
}

/// Resolves `Chunk::Abbreviation` items to their respective string values.
fn resolve_abbreviations(s: Vec<RawChunk>, map: &HashMap<&str, &str>) -> Vec<RawChunk> {
    let mut res: Vec<RawChunk> = vec![];

    for elem in s.into_iter() {
        if let RawChunk::Abbreviation(x) = elem {
            // FIXME: Prevent cyclic evaluation.
            let val = map.get(x.as_str()).and_then(|&s| {
                Some(resolve_abbreviations(parse_string(s, false)?.0, map))
            });

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
    let mut res: Vec<RawChunk> = vec![];
    let mut iter = values.into_iter().peekable();

    fn modify_args(
        args: Option<Vec<RawChunk>>,
        verb: bool,
        f: impl Fn(Option<Vec<RawChunk>>) -> Option<Vec<RawChunk>>,
    ) -> Option<Vec<RawChunk>> {
        if verb {
            f(args).map(|a| a.into_iter().map(|a| a.to_preserved()).collect())
        } else {
            f(args)
        }
    }

    fn last_char_combine(
        v: Option<Vec<RawChunk>>,
        combine: char,
    ) -> Option<Vec<RawChunk>> {
        let mut v = v?;
        if let Some(item) = v.pop() {
            if let Some(ds) = item.display_string() {
                let len = ds.len();
                let lc = if ds.len() > 0 && ds.is_char_boundary(len - 1) {
                    ds.chars().last().and_then(|c| char::compose(c, combine))
                } else {
                    None
                };

                let item = if let Some(lc) = lc {
                    let mut s = (&ds[.. len - 1]).to_string();
                    s.push(lc);
                    item.reset_string(s)
                } else {
                    item
                };
                v.push(item);
            } else {
                v.push(item);
            }
        }
        Some(v)
    }

    fn to_value(s: &str, args: Option<Vec<RawChunk>>) -> Option<Vec<RawChunk>> {
        let mut start = vec![RawChunk::Normal(s.to_string())];

        if let Some(args) = args {
            start.extend(args);
        }

        Some(start)
    }

    while let Some(val) = iter.next() {
        let (cmd, verb, args) = match val {
            RawChunk::CommandName(cmd, verb, args) => {
                (cmd, verb, args.map(|a| resolve_latex_commands(a)))
            }
            chunk => {
                res.push(chunk);
                continue;
            }
        };

        let next = match cmd.as_str() {
            "LaTeX" => modify_args(args, true, |v| to_value("LaTeX", v)),
            "TeX" => modify_args(args, true, |v| to_value("TeX", v)),
            "textendash" => modify_args(args, verb, |v| to_value("–", v)),
            "textemdash" => modify_args(args, verb, |v| to_value("—", v)),
            "aa" => modify_args(args, verb, |v| to_value("å", v)),
            "AA" => modify_args(args, verb, |v| to_value("Å", v)),
            "l" => modify_args(args, verb, |v| to_value("ł", v)),
            "L" => modify_args(args, verb, |v| to_value("Ł", v)),
            "i" => modify_args(args, verb, |v| to_value("ı", v)),
            "oe" => modify_args(args, verb, |v| to_value("œ", v)),
            "OE" => modify_args(args, verb, |v| to_value("Œ", v)),
            "ae" => modify_args(args, verb, |v| to_value("æ", v)),
            "AE" => modify_args(args, verb, |v| to_value("Æ", v)),
            "o" if args.is_none() => modify_args(args, verb, |v| to_value("ø", v)),
            "O" => modify_args(args, verb, |v| to_value("Ø", v)),
            "ss" => modify_args(args, verb, |v| to_value("ß", v)),
            "SS" => modify_args(args, verb, |v| to_value("ẞ", v)),
            "`" => modify_args(args, verb, |v| last_char_combine(v, '\u{300}')),
            "´" => modify_args(args, verb, |v| last_char_combine(v, '\u{301}')),
            "'" => modify_args(args, verb, |v| last_char_combine(v, '\u{301}')),
            "^" => modify_args(args, verb, |v| last_char_combine(v, '\u{302}')),
            "~" => modify_args(args, verb, |v| last_char_combine(v, '\u{303}')),
            "=" => modify_args(args, verb, |v| last_char_combine(v, '\u{304}')),
            "u" => modify_args(args, verb, |v| last_char_combine(v, '\u{306}')),
            "." => modify_args(args, verb, |v| last_char_combine(v, '\u{307}')),
            "\"" => modify_args(args, verb, |v| last_char_combine(v, '\u{308}')),
            "r" => modify_args(args, verb, |v| last_char_combine(v, '\u{30A}')),
            "H" => modify_args(args, verb, |v| last_char_combine(v, '\u{30B}')),
            "v" => modify_args(args, verb, |v| last_char_combine(v, '\u{30C}')),
            "d" => modify_args(args, verb, |v| last_char_combine(v, '\u{323}')),
            "c" => modify_args(args, verb, |v| last_char_combine(v, '\u{327}')),
            "k" => modify_args(args, verb, |v| last_char_combine(v, '\u{328}')),
            "b" => modify_args(args, verb, |v| last_char_combine(v, '\u{332}')),
            "o" => modify_args(args, verb, |v| last_char_combine(v, '\u{338}')),
            _ => modify_args(args, verb, |v| v),
        };

        if let Some(v) = next {
            res.extend(v)
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
                res.push(RawChunk::PreserveCase(take(&mut verbatim)));
            }
            normal += &x;
        } else if let RawChunk::PreserveCase(x) = elem {
            if !normal.is_empty() {
                res.push(RawChunk::Normal(take(&mut normal)));
            }
            verbatim += &x;
        } else {
            if !verbatim.is_empty() {
                res.push(RawChunk::PreserveCase(take(&mut verbatim)));
            }

            if !normal.is_empty() {
                res.push(RawChunk::Normal(take(&mut normal)));
            }

            res.push(elem);
        }
    }

    if !verbatim.is_empty() {
        res.push(RawChunk::PreserveCase(verbatim));
    }

    if !normal.is_empty() {
        res.push(RawChunk::Normal(normal));
    }

    res
}

/// Characters that can be escaped.
pub fn is_escapable(c: char) -> bool {
    match c {
        '&' | '%' | '{' | '}' | '$' | '_' | '\\' => true,
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
        RawChunk::PreserveCase(s.to_string())
    }
    fn C(s: &str, verb: bool, args: Option<Vec<RawChunk>>) -> RawChunk {
        RawChunk::CommandName(s.to_string(), verb, args)
    }

    #[test]
    fn test_process() {
        let res = parse_string("abc # \"good {TIMES}\" # hi # you # \"last\"", false).unwrap().0;
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
        let res = parse_string("\"\\\"{A}ther und {\"\\LaTeX \"} {\\relax for you\\}}\"", false).unwrap().0;
        assert_eq!(res[0], C("\"", false, Some(vec![N("A")])));
        assert_eq!(res[1], N("ther und "));
        assert_eq!(res[2], V("\""));
        assert_eq!(res[3], C("LaTeX", true, None));
        assert_eq!(res[4], V("\""));
        assert_eq!(res[5], N(" "));
        assert_eq!(res[6], C("relax", true, None));
        assert_eq!(res[7], V("for you}"));
        assert_eq!(res.len(), 8);

        let res = parse_string("\"M\\\"etal S\\= ound\"", false).unwrap().0;
        assert_eq!(res[0], N("M"));
        assert_eq!(res[1], C("\"", false, Some(vec![N("e")])));
        assert_eq!(res[2], N("tal S"));
        assert_eq!(res[3], C("=", false, Some(vec![N("o")])));
        assert_eq!(res[4], N("und"));
    }

    #[test]
    fn test_resolve_strings() {
        let res = parse_string("a # b # c # \" \\\"{a} and others\"", false).unwrap().0;
        let mut map = HashMap::new();
        map.insert("a", "\"trees\"");
        map.insert("b", "\"bushes\"");
        map.insert("c", "a # \" and \" # b");

        let res = resolve_abbreviations(res, &map);
        assert_eq!(res[0], N("treesbushestrees and bushes "));
        assert_eq!(res[1], C("\"", false, Some(vec![N("a")])));
        assert_eq!(res[2], N(" and others"));

        let map = HashMap::new();
        let res = resolve_abbreviations(parse_string("Jan # \"~12\"", false).unwrap().0, &map);
        assert_eq!(res[0], N("January\u{A0}12"));
    }

    #[test]
    fn test_math() {
        let res = parse_string("{The $11^{th}$ International Conference on How To Make \\$\\$}", false).unwrap().0;
        assert_eq!(res[0], N("The $11^{th}$ International Conference on How To Make $$"));
        assert_eq!(res.len(), 1);
    }

    #[test]
    fn test_first_escape() {
        let res = parse_string("{\\\\\" in the eye}", false).unwrap().0;
        assert_eq!(res[0], N("\\\" in the eye"));
        assert_eq!(res.len(), 1);
    }

    #[test]
    fn test_commands() {
        // let res = resolve_latex_commands(parse_string("{\\LaTeX{}~is gr\\~e\\`at\\o", false).unwrap().0);
        // assert_eq!(res[0], V("LaTeX"));
        // assert_eq!(res[1], N("\u{00A0}is grẽàtø"));
        let res = resolve_latex_commands(parse_string("{Bose\\textendash{}Einstein}", false).unwrap().0);
        assert_eq!(res[0], N("Bose–Einstein"));
    }

    #[test]
    fn test_nested_commands() {
        // let res = resolve_latex_commands(parse_string("{\\textendash{\\`a}}", false).unwrap().0);
        // assert_eq!(res[0], N("–à"));
        let res = resolve_latex_commands(parse_string("{A{\\ss}{\\ss}{\\ss}mann}", false).unwrap().0);
        assert_eq!(res[0], N("A"));
        assert_eq!(res[1], V("ßßß"));
        assert_eq!(res[2], N("mann"));
    }

    #[test]
    fn test_raw_year() {
        let res = parse_string("1975", false).unwrap().0;
        assert_eq!(res[0], N("1975"));
    }
}
