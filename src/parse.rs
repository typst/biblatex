use std::collections::HashMap;
use std::mem::take;

use anyhow::anyhow;
use unicode_normalization::char;

use crate::dtypes::{ChunkExt, IntOrChunks, Person};
use crate::syntax::parse_file;

/// Parse a vector of collection entries from a source string.
pub fn parse_collection<'s>(src: &'s str, allow_bibtex: bool) -> Vec<CollectionEntry> {
    let file = parse_file(src, allow_bibtex);
    let strings = &file.strings;

    file.entries
        .into_iter()
        .map(|entry| CollectionEntry {
            cite_key: entry.cite_key.to_string(),
            entry_type: entry.entry_type.to_lowercase().to_string(),
            fields: entry
                .fields
                .into_iter()
                .map(|(key, value)| {
                    let resolved = resolve(process_string(value), strings);
                    let evaluated = eval_latex_commands(resolved);
                    (key.to_string(), evaluated)
                })
                .collect(),
        })
        .collect()
}

/// A bibliography entry in its intermediate form (parsed into Chunks, but not yet
/// the appropriate data types).
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct CollectionEntry {
    /// The citation key.
    pub cite_key: String,
    /// Denotes the type of bibliography item (e.g. `article`).
    pub entry_type: String,
    /// Maps from field names to their associated chunk vectors.
    pub fields: HashMap<String, Vec<Chunk>>,
}

impl CollectionEntry {
    /// Get the chunk slice for a field.
    pub fn get(&self, key: &str) -> Option<&[Chunk]> {
        self.fields.get(&key.to_lowercase()).map(AsRef::as_ref)
    }

    fn get_opt<'a>(&'a self, key: &str) -> Option<&'a [Chunk]> {
        self.props.get(&key.to_lowercase()).map(|v| v.as_slice())
    }

    pub fn get_date<'a>(&'a self) -> Result<Date, anyhow::Error> {
        let date_field = self.get_opt("date");
        if let Some(date) = date_field {
            let date: Vec<Chunk> = Vec::from(date);
            date.parse::<Date>()
        } else {
            Date::new_from_three_fields(
                self.get_opt("year"),
                self.get_opt("month"),
                self.get_opt("day")
            )
        }
    }
}

macro_rules! fields {
    ($($getter:ident: $field_name:expr $(=> $res:ty)?),* $(,)*) => {
        impl CollectionEntry {
            $(
                #[doc = "Extracts and parses the `"]
                #[doc = $field_name]
                #[doc = "` field."]
                pub fn $getter(&self) -> Result<fields!(@type $($res)?), anyhow::Error> {
                    self.get($field_name)
                        .ok_or_else(|| anyhow!("The {} field is not present", $field_name))
                        $(.and_then(|chunks| chunks.parse::<$res>()))?
                }
            )*
        }
    };

    (@type) => {&[Chunk]};
    (@type $res:ty) => {$res};
}

fields! {
    // Fields without a specified return type simply return `&[Chunk]`.
    get_address: "address",
    get_annote: "annote",
    get_author: "author" => Vec<Person>,
    get_booktitle: "booktitle",
    get_chapter: "chapter",
    get_edition: "edition" => IntOrChunks,
    get_editor: "editor" => Vec<Person>,
    get_howpublished: "howpublished",
    get_institution: "institution",
    get_journal: "journal",
    get_note: "note",
    get_number: "number" => i64,
    get_organization: "organization",
    get_pages: "pages" => Vec<std::ops::Range<u32>>,
    get_publisher: "publisher" => Vec<Vec<Chunk>>,
    get_school: "school",
    get_series: "series",
    get_title: "title",
    get_type: "type",
    get_volume: "volume",
}

/// A Chunk represents an element in a Bib(La)TeX field value.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Chunk {
    /// Values nested in braces that are to be printed like specified
    /// in the file. Escapes keywords.
    ///
    /// Example: `"Inside {NASA}"` or `{Memes are {gReAT}}`.
    Verbatim(String),
    /// Normal values within quotes or single braces subject to
    /// capitalization formatting.
    Normal(String),
    /// BibTeX allows strings to be saved and concatenated later.
    /// This Chunk is a reference to a named string to be resolved.
    ///
    /// Example: `author1 # " and " # author2`
    Resolve(String),
    /// LaTeX command names within quotes or braces.
    /// May be followed by `Chunk::CommandArgs` in Chunk slices.
    CommandName(String, bool),
    /// LaTeX command arguments.
    /// Must be preceeded by `Chunk::CommandName` in Chunk slices.
    CommandArgs(String),
}

/// Create a Chunk vector from field value string references.
fn process_string(s: &str) -> Vec<Chunk> {
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
    let mut vals: Vec<Chunk> = vec![];
    let mut allow_resolvable = true;
    let mut is_math = false;
    let mut expect_arg = false;
    let mut esc_cmd_mode = EscCommandMode::Neither;

    for c in s.chars().peekable() {
        if c == '$' && esc_cmd_mode != EscCommandMode::Both {
            is_math = !is_math;
        }

        match c {
            _ if esc_cmd_mode == EscCommandMode::Both && is_escapable(c) => {
                let _success = if let Some(x) = vals.last_mut() {
                    if let Chunk::Normal(s) = x {
                        s.push(c);
                        true
                    } else if let Chunk::Verbatim(s) = x {
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
                vals.push(Chunk::CommandArgs(c.to_string()));
                stack.pop();
                expect_arg = false;
            }

            _ if esc_cmd_mode != EscCommandMode::Neither && !c.is_whitespace() => {
                match vals.last_mut() {
                    Some(Chunk::CommandName(s, _))
                        if esc_cmd_mode == EscCommandMode::OnlyCommand =>
                    {
                        s.push(c);
                    }
                    _ => {
                        esc_cmd_mode = EscCommandMode::OnlyCommand;
                        vals.push(Chunk::CommandName(c.to_string(), stack.len() > 1));
                        stack.push(Symbols::Command);
                        if is_single_char_func(c) {
                            esc_cmd_mode = EscCommandMode::Neither;
                            expect_arg = true;
                        }
                    }
                };

                continue;
            }

            _ if stack.last() == Some(&Symbols::Command) => match vals.last_mut() {
                Some(Chunk::CommandArgs(s)) => s.push(c),
                _ => vals.push(Chunk::CommandArgs(c.to_string())),
            },

            _ if stack.is_empty() => match vals.last_mut() {
                Some(Chunk::Resolve(s)) if !allow_resolvable => s.push(c),
                _ if allow_resolvable => {
                    allow_resolvable = false;
                    vals.push(Chunk::Resolve(c.to_string()))
                }
                _ => {}
            },

            '~' if !stack.is_empty() => match vals.last_mut() {
                Some(Chunk::Normal(s)) => s.push('\u{00A0}'),
                Some(Chunk::Verbatim(s)) => s.push('\u{00A0}'),
                _ if stack.len() == 1 => {
                    vals.push(Chunk::Normal('\u{00A0}'.to_string()));
                }
                _ => {
                    vals.push(Chunk::Verbatim('\u{00A0}'.to_string()));
                }
            },

            _ if stack.len() == 1 => match vals.last_mut() {
                Some(Chunk::Normal(s)) => s.push(c),
                _ => vals.push(Chunk::Normal(c.to_string())),
            },

            _ => match vals.last_mut() {
                Some(Chunk::Verbatim(s)) => s.push(c),
                _ => vals.push(Chunk::Verbatim(c.to_string())),
            },
        }

        esc_cmd_mode = EscCommandMode::Neither;
    }

    vals
}

/// Resolves `Chunk::Resolve` items to their respective string values.
fn resolve(s: Vec<Chunk>, map: &HashMap<&str, &str>) -> Vec<Chunk> {
    let mut res: Vec<Chunk> = vec![];

    for elem in s.into_iter() {
        if let Chunk::Resolve(x) = elem {
            // FIXME: Prevent cyclic evaluation.
            let val = map.get(x.as_str()).map(|&s| resolve(process_string(s), map));

            if let Some(mut x) = val {
                res.append(&mut x);
            } else if let Some(x) = get_month_for_abbr(&x) {
                res.push(Chunk::Normal(x.0));
            }
        } else {
            res.push(elem);
        }
    }

    flatten(res)
}

/// Simplifies a chunk vector by collapsing neighboring Normal or Verbatim chunks.
fn flatten(s: Vec<Chunk>) -> Vec<Chunk> {
    let mut normal = String::new();
    let mut verbatim = String::new();
    let mut res: Vec<Chunk> = vec![];

    for elem in s {
        if let Chunk::Normal(x) = elem {
            if !verbatim.is_empty() {
                res.push(Chunk::Verbatim(take(&mut verbatim)));
            }
            normal += &x;
        } else if let Chunk::Verbatim(x) = elem {
            if !normal.is_empty() {
                res.push(Chunk::Normal(take(&mut normal)));
            }
            verbatim += &x;
        } else {
            if !verbatim.is_empty() {
                res.push(Chunk::Verbatim(take(&mut verbatim)));
            }

            if !normal.is_empty() {
                res.push(Chunk::Normal(take(&mut normal)));
            }

            res.push(elem);
        }
    }

    if !verbatim.is_empty() {
        res.push(Chunk::Verbatim(verbatim));
    }

    if !normal.is_empty() {
        res.push(Chunk::Normal(normal));
    }

    res
}

/// Best-effort evaluation of LaTeX commands with a focus on diacritics.
/// Will dump the command arguments if evaluation not possible.
/// Nested commands are not supported.
fn eval_latex_commands(values: Vec<Chunk>) -> Vec<Chunk> {
    let mut res: Vec<Chunk> = vec![];
    let mut iter = values.into_iter().peekable();

    fn modify_args(
        val: Option<Chunk>,
        verb: bool,
        f: impl Fn(String) -> String,
    ) -> Option<Chunk> {
        val.map(|val| {
            if let Chunk::CommandArgs(args) = val {
                to_value(&f(args), verb)
            } else {
                val
            }
        })
    }

    fn last_char_combine(mut v: String, combine: char) -> String {
        if let Some(c) = v.pop().and_then(|c| char::compose(c, combine)) {
            v.push(c);
        }
        v
    }

    fn to_value(s: &str, verb: bool) -> Chunk {
        if verb {
            Chunk::Verbatim(s.to_string())
        } else {
            Chunk::Normal(s.to_string())
        }
    }

    while let Some(val) = iter.next() {
        let (cmd, verb) = match val {
            Chunk::CommandName(cmd, verb) => (cmd, verb),
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
            "o" if !matches!(iter.peek(), Some(Chunk::CommandArgs(_))) => {
                Some(to_value("ø", verb))
            }
            "O" => Some(to_value("Ø", verb)),
            "ss" => Some(to_value("ß", verb)),
            "SS" => Some(to_value("ẞ", verb)),
            "`" => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{300}')),
            "´" => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{301}')),
            "'" => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{301}')),
            "^" => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{302}')),
            "~" => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{303}')),
            "=" => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{304}')),
            "u" => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{306}')),
            "." => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{307}')),
            "\"" => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{308}')),
            "r" => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{30A}')),
            "H" => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{30B}')),
            "v" => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{30C}')),
            "d" => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{323}')),
            "c" => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{327}')),
            "k" => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{328}')),
            "b" => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{332}')),
            "o" => modify_args(iter.next(), verb, |v| last_char_combine(v, '\u{338}')),
            "t" => modify_args(iter.next(), verb, |mut v| {
                // FIXME: This one does not seem to work.
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
    }

    flatten(res)
}

/// Characters that can be escaped.
fn is_escapable(c: char) -> bool {
    match c {
        '&' | '%' | '{' | '}' | ',' | '$' | '\'' | '_' => true,
        _ => false,
    }
}

/// Characters that are the name of a single-char command
/// that automatically terminates.
fn is_single_char_func(c: char) -> bool {
    match c {
        '"' | '´' | '`' | '^' | '~' | '=' | '.' => true,
        _ => false,
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
#[rustfmt::skip]
mod tests {
    use std::collections::HashMap;

    use super::{eval_latex_commands, process_string, resolve, Chunk};

    fn R(s: &str) -> Chunk {
        Chunk::Resolve(s.to_string())
    }
    fn N(s: &str) -> Chunk {
        Chunk::Normal(s.to_string())
    }
    fn V(s: &str) -> Chunk {
        Chunk::Verbatim(s.to_string())
    }
    fn C(s: &str, verb: bool) -> Chunk {
        Chunk::CommandName(s.to_string(), verb)
    }
    fn CA(s: &str) -> Chunk {
        Chunk::CommandArgs(s.to_string())
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
        let res = process_string("\"\\\"{A}ther und {\"\\LaTeX \"} {\\relax for you\\}}\"");
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
    fn test_resolve_strings() {
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

        let res = process_string("Jan # \"~12\"");
        let map = HashMap::new();
        let res = resolve(res, &map);
        assert_eq!(res[0], N("January\u{A0}12"));
    }

    #[test]
    fn test_math() {
        let res = process_string("{The $11^{th}$ International Conference on How To Make \\$\\$}");
        assert_eq!(res[0], N("The $11^{th}$ International Conference on How To Make $$"));
        assert_eq!(res.len(), 1);
    }

    #[test]
    fn test_commands() {
        let res = eval_latex_commands(process_string("{\\LaTeX{}~is gr\\~e\\`at\\o \\t{oo}"));
        assert_eq!(res[0], V("LaTeX"));
        assert_eq!(res[1], N("\u{00A0}is grẽàtøo\u{361}o"));
    }
}