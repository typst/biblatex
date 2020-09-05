use std::collections::HashMap;
use std::iter::Peekable;
use std::str::Chars;

use unicode_xid::UnicodeXID;

#[derive(Debug, PartialEq)]
/// Symbols that may be found when parsing a file.
enum Symbols {
    Quotes,
    Braces,
}

#[derive(Clone, Debug, Default)]
/// A Bib(La)TeX file entry as directly extracted, the strings are not yet parsed.
pub struct BiblatexEntry<'s> {
    /// The bibliography item's type, e.g. `inbook`.
    pub entry_type: &'s str,
    /// A map of field names to field values.
    pub props: HashMap<&'s str, &'s str>,
}

#[derive(Clone, Debug)]
/// A Bib(La)TeX file's most literal representation, the strings are not yet parsed.
pub struct BiblatexFile<'s> {
    /// TeX commands to be prepended to the document, only supported by BibTeX.
    pub preamble: String,
    pub entries: Vec<(&'s str, BiblatexEntry<'s>)>,
    /// Map of reusable strings, only supported by BibTeX.
    pub strings: HashMap<&'s str, &'s str>,
}

enum ParseMode {
    Outside,
    Type,
    KeyMode,
    PreambleMode,
    EntryMode,
}

/// Backing struct for parsing a Bib(La)TeX file into a `BiblatexFile` struct.
pub struct BiblatexParser<'s> {
    allow_bibtex: bool,
    src: &'s str,
    mode: ParseMode,
    index: usize,
    comment: bool,
    iter: Peekable<Chars<'s>>,
    res: BiblatexFile<'s>,
}

/// Characters allowable in identifiers like cite keys.
fn is_ident(c: char, first: bool) -> bool {
    let unpermissable = "\"#'(),={}%\\~";
    let interpunct = ":<->_";

    !unpermissable.contains(c)
        && if first {
            UnicodeXID::is_xid_start(c)
        } else {
            UnicodeXID::is_xid_continue(c) || interpunct.contains(c)
        }
}

impl<'s> BiblatexParser<'s> {
    /// Constructs a new parser.
    pub fn new(src: &'s str, allow_bibtex: bool) -> Self {
        Self {
            allow_bibtex,
            src,
            mode: ParseMode::Outside,
            index: 0,
            iter: src.chars().peekable(),
            comment: false,
            res: BiblatexFile {
                preamble: String::new(),
                entries: vec![],
                strings: HashMap::new(),
            },
        }
    }

    /// Parses the file, consuming the parser in the process.
    pub fn parse(mut self) -> BiblatexFile<'s> {
        while let Some(c) = self.eat() {
            if c == '@' && !self.comment {
                self.parse_entry();
            } else if c == '%' {
                self.comment = true;
            } else if c == '\n' || c == '\r' {
                self.comment = false;
            }
        }

        self.res
    }

    /// Parse a bibliography entry.
    fn parse_entry(&mut self) {
        self.mode = ParseMode::Type;

        let type_start = self.index;
        let mut type_end = self.index;
        let mut key_start: usize = 0;
        let mut key_end: usize = 0;
        self.mode = ParseMode::Type;
        let mut entry = BiblatexEntry::default();
        let mut is_string = false;

        while let Some(c) = self.peek() {
            match self.mode {
                ParseMode::Type => {
                    if is_ident(c, type_start == type_end) {
                        self.eat();
                        type_end = self.index;
                    } else {
                        entry.entry_type = &self.src[type_start .. type_end];
                        if c.is_whitespace() {
                            self.eat();
                        } else if c == '{' {
                            let lower_type =
                                &self.src[type_start .. type_end].to_lowercase();
                            self.eat();

                            if lower_type == "string" {
                                self.mode = ParseMode::EntryMode;
                                is_string = true;
                            } else if lower_type == "preamble" {
                                self.mode = ParseMode::PreambleMode;
                            } else {
                                key_start = self.index;
                                key_end = self.index;
                                self.mode = ParseMode::KeyMode;
                            }
                        } else {
                            // TODO Invalid
                            self.mode = ParseMode::Outside;
                            break;
                        }
                    }
                }

                ParseMode::KeyMode => {
                    if is_ident(c, key_start == key_end) {
                        self.eat();
                        key_end = self.index;
                    } else if c.is_whitespace() {
                        self.eat();
                    } else if c == ',' {
                        self.eat();
                        self.mode = ParseMode::EntryMode;
                    } else {
                        // TODO Invalid
                        self.mode = ParseMode::Outside;
                        break;
                    }
                }

                ParseMode::PreambleMode => {
                    self.skip_ws();

                    // This does not allow string concatenation in preambles
                    if c == '\"' {
                        self.eat();
                        while let Some(c) = self.eat() {
                            if c == '\"' {
                                break;
                            }
                            self.res.preamble.push(c);
                        }
                    }

                    self.mode = ParseMode::Outside;
                }

                ParseMode::EntryMode => {
                    self.skip_ws();
                    if self.peek() == Some('}') {
                        self.mode = ParseMode::Outside;
                        continue;
                    }
                    let s = self.read_prop().expect("Hallo");
                    if is_string {
                        self.res.strings.insert(s.0, s.1);
                    } else {
                        entry.props.insert(s.0, s.1);
                    }
                }
                _ => break,
            }
        }
        if !is_string {
            self.res.entries.push((&self.src[key_start .. key_end], entry));
        }

        self.mode = ParseMode::Outside;
    }

    /// Read a field.
    fn read_prop(&mut self) -> Result<(&'s str, &'s str), ()> {
        self.skip_ws();

        let start = self.index;
        let mut end = self.index;

        while let Some(c) = self.peek() {
            if is_ident(c, start == end) {
                self.eat();
                end = self.index;
            } else {
                break;
            }
        }

        let name = &self.src[start .. end];
        while let Some(c) = self.eat() {
            if c == '=' {
                break;
            }
        }
        self.skip_ws();

        let mut stack: Vec<Symbols> = vec![];
        let val_start = self.index;
        let mut val_end = self.index;
        let mut escape = false;

        while let Some(c) = self.eat() {
            match c {
                '\\' => {
                    escape = true;
                    continue;
                }
                '{' if escape => {}
                '}' if escape => {}
                '"' if escape => {}
                ',' if stack.is_empty() => {
                    break;
                }
                '}' if stack.is_empty() => {
                    self.mode = ParseMode::Outside;
                    println!("name {}", name);
                    break;
                }
                '"' if stack.last() == Some(&Symbols::Quotes) => {
                    stack.pop();
                }
                '"' if stack.is_empty() => {
                    stack.push(Symbols::Quotes);
                }
                '{' => {
                    stack.push(Symbols::Braces);
                }
                '}' => {
                    let x = stack.pop();
                    if x != Some(Symbols::Braces) {
                        return Err(());
                    }
                }
                _ => {}
            }
            escape = false;
            val_end = self.index;
        }

        Ok((name, &self.src[val_start .. val_end]))
    }

    /// Get the next character without advancing the parsing file iterator.
    fn peek(&mut self) -> Option<char> {
        self.iter.peek().copied()
    }

    /// Advance the parsing file iterator to the next non-whitespace or comment
    /// character.
    fn skip_ws(&mut self) {
        while let Some(c) = self.peek() {
            if c == '%' {
                self.comment = true;
                self.eat();
                continue;
            } else if c == '\n' || c == '\r' {
                self.comment = false;
            } else if self.comment {
                self.eat();
                continue;
            }

            if c.is_whitespace() || c == '\n' || c == '\r' {
                self.eat();
            } else {
                break;
            }
        }
    }

    /// Advance the parsing file iterator by one and return the consumed character.
    fn eat(&mut self) -> Option<char> {
        let c = self.iter.next()?;
        self.index += c.len_utf8();

        Some(c)
    }
}

#[cfg(test)]
mod tests {
    use super::BiblatexParser;

    macro_rules! bt {
        ($src:expr, $mode:expr $(,)?) => {{
            let p = BiblatexParser::new($src, $mode);
            p.parse()
        }};
    }

    fn test_prop<'a>(prop_name: &'a str, prop: &'a str) -> String {
        let scaffold = "@article{test, ";
        let mut test_obj = scaffold.to_string() + prop_name;
        test_obj.push('=');
        test_obj.push_str(prop);
        test_obj.push('}');
        let bt = bt!(&test_obj, true);
        let article = &bt.entries[0].1;
        article.props.get(prop_name).expect("fail").to_string()
    }

    #[test]
    fn it_works() {
        let bt = bt!(
            "@article{haug2020,\n\n  title = \"Great proceedings\\{\",\n   year=2002,\n   author={Haug, {Martin} and Haug, Gregor}}",
            true
        );

        let article = &bt.entries[0].1;
        assert_eq!(article.entry_type, "article");
        assert_eq!(
            *article.props.get("title").expect("fail"),
            "\"Great proceedings\\{\""
        );
        assert_eq!(*article.props.get("year").expect("fail"), "2002");
        assert_eq!(
            *article.props.get("author").expect("fail"),
            "{Haug, {Martin} and Haug, Gregor}"
        );
    }

    #[test]
    fn test_strings() {
        let bt = bt!("@string{BT = \"bibtex\"}", true);

        let &bts = bt.strings.get("BT").expect("fail");
        assert_eq!(bts, "\"bibtex\"");
    }

    #[test]
    fn test_escape() {
        assert_eq!(
            test_prop("author", "{Mister A\\}\"B\"}"),
            "{Mister A\\}\"B\"}"
        );
    }
}
