//! Low-level representation of a bibliography file.

use std::collections::HashMap;
use std::fmt;

use crate::scanner::{is_id_continue, is_id_start, is_newline, Scanner};

/// A literal representation of a bibliography file, with abbreviations not yet
/// resolved.
#[derive(Debug, Clone)]
pub struct RawBibliography<'s> {
    /// TeX commands to be prepended to the document, only supported by BibTeX.
    pub preamble: String,
    /// The collection of citation keys and bibliography entries.
    pub entries: Vec<RawEntry<'s>>,
    /// A map of reusable abbreviations, only supported by BibTeX.
    pub abbreviations: HashMap<&'s str, &'s str>,
}

/// A raw extracted entry, with abbreviations not yet resolved.
#[derive(Debug, Clone)]
pub struct RawEntry<'s> {
    /// The citation key.
    pub key: &'s str,
    /// Denotes the type of bibliographic item (e.g. `article`).
    pub kind: &'s str,
    /// Maps from field names to their values.
    pub fields: HashMap<&'s str, &'s str>,
}

impl<'s> RawBibliography<'s> {
    /// Parse a raw bibliography from a source string.
    pub fn parse(src: &'s str) -> Self {
        BiblatexParser::new(src).parse().0
    }
}

/// Backing struct for parsing a Bib(La)TeX file into a [`RawBibliography`].
struct BiblatexParser<'s> {
    s: Scanner<'s>,
    res: RawBibliography<'s>,
}

#[derive(Debug, Clone)]
struct ParseError {
    span: std::ops::Range<usize>,
    kind: ParseErrorKind,
}

impl ParseError {
    fn new(span: std::ops::Range<usize>, kind: ParseErrorKind) -> Self {
        Self { span, kind }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}-{}", self.kind, self.span.start, self.span.end)
    }
}

#[derive(Debug, Copy, Clone)]
enum ParseErrorKind {
    UnexpectedEof,
    Expected(Token),
}

#[derive(Debug, Copy, Clone)]
enum Token {
    Identifier,
    OpeningBrace,
    ClosingBrace,
    Comma,
    QuotationMark,
    Equals,
}

impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::UnexpectedEof => write!(f, "unexpected end of file"),
            Self::Expected(token) => write!(f, "expected {}", token),
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", match self {
            Self::Identifier => "identifier",
            Self::OpeningBrace => "opening brace",
            Self::ClosingBrace => "closing brace",
            Self::Comma => "comma",
            Self::QuotationMark => "double quote",
            Self::Equals => "equals",
        })
    }
}

impl<'s> BiblatexParser<'s> {
    /// Constructs a new parser.
    pub fn new(src: &'s str) -> Self {
        Self {
            s: Scanner::new(src),
            res: RawBibliography {
                preamble: String::new(),
                entries: vec![],
                abbreviations: HashMap::new(),
            },
        }
    }

    /// Parses the file, consuming the parser in the process.
    pub fn parse(mut self) -> (RawBibliography<'s>, Vec<ParseError>) {
        let mut errors = vec![];

        while !self.s.eof() {
            self.skip_trivia();
            match self.s.peek() {
                Some('@') => {
                    if let Err(e) = self.entry() {
                        errors.push(e);
                    }
                }
                Some(_) => {
                    self.s.eat();
                }
                None => break,
            }
        }

        (self.res, errors)
    }

    /// Skip the whitespace in the file.
    fn skip_ws(&mut self) {
        self.s.eat_while(|c| c.is_whitespace());
    }

    /// Skip the newlines and whitespace in the file.
    fn skip_trivia(&mut self) {
        self.s.eat_while(|c| c.is_whitespace() || is_newline(c));
    }

    /// Eat a comma.
    fn comma(&mut self) -> Result<(), ParseError> {
        if !self.s.eat_if(',') {
            return Err(ParseError::new(
                self.here(),
                ParseErrorKind::Expected(Token::Comma),
            ));
        }

        Ok(())
    }

    /// Eat a delimiter.
    fn brace(&mut self, open: bool) -> Result<(), ParseError> {
        let (brace, token) = if open {
            ('{', Token::OpeningBrace)
        } else {
            ('}', Token::ClosingBrace)
        };

        let peeked = self.s.peek();

        if peeked == Some(brace) || peeked == Some('\"') {
            self.s.eat();
            Ok(())
        } else {
            Err(ParseError::new(
                self.here(),
                ParseErrorKind::Expected(token),
            ))
        }
    }

    /// Eat a quote.
    fn quote(&mut self) -> Result<(), ParseError> {
        if !self.s.eat_if('"') {
            Err(ParseError::new(
                self.here(),
                ParseErrorKind::Expected(Token::QuotationMark),
            ))
        } else {
            Ok(())
        }
    }

    /// Eat an equals sign.
    fn equals(&mut self) -> Result<(), ParseError> {
        if !self.s.eat_if('=') {
            Err(ParseError::new(
                self.here(),
                ParseErrorKind::Expected(Token::Equals),
            ))
        } else {
            Ok(())
        }
    }

    /// Eat a string.
    fn string(&mut self) -> Result<(), ParseError> {
        self.quote()?;

        while let Some(c) = self.s.peek() {
            match c {
                '"' => {
                    self.quote()?;
                    return Ok(());
                }
                '\\' => {
                    self.s.eat_assert('\\');
                    self.s.eat();
                }
                _ => {
                    self.s.eat();
                }
            }
        }

        Err(ParseError::new(self.here(), ParseErrorKind::UnexpectedEof))
    }

    /// Eat a braced value.
    fn braced(&mut self) -> Result<(), ParseError> {
        self.brace(true)?;
        let mut braces = 0;

        while let Some(c) = self.s.peek() {
            match c {
                '{' => {
                    self.brace(true)?;
                    braces += 1;
                }
                '}' => {
                    self.brace(false)?;
                    if braces == 0 {
                        return Ok(());
                    }
                    braces -= 1;
                }
                '\\' => {
                    self.s.eat_assert('\\');
                    self.s.eat();
                }
                _ => {
                    self.s.eat();
                }
            }
        }

        Err(ParseError::new(self.here(), ParseErrorKind::UnexpectedEof))
    }

    /// Eat an element of an abbreviation.
    fn abbr_element(&mut self) -> Result<(), ParseError> {
        match self.s.peek() {
            Some(c) if is_id_start(c) => self.ident().map(|_| ()),
            _ => self.string().map(|_| ()),
        }
    }

    /// Eat an abbreviation field.
    fn abbr_field(&mut self) -> Result<(), ParseError> {
        loop {
            self.abbr_element()?;
            self.skip_ws();
            if !self.s.eat_if('#') {
                break;
            }
            self.skip_ws();
        }

        Ok(())
    }

    /// Eat a field.
    fn field(&mut self) -> Result<(&'s str, &'s str), ParseError> {
        let key = self.ident()?;
        self.skip_ws();
        self.equals()?;
        self.skip_ws();

        let value_pos = self.s.index();
        match self.s.peek() {
            Some('{') => self.braced()?,
            Some(_) => self.abbr_field()?,
            None => {
                return Err(ParseError::new(self.here(), ParseErrorKind::UnexpectedEof));
            }
        }

        self.skip_ws();

        Ok((key, self.s.eaten_from(value_pos)))
    }

    /// Eat fields.
    fn fields(&mut self) -> Result<HashMap<&'s str, &'s str>, ParseError> {
        let mut fields = HashMap::new();

        while !self.s.eof() {
            self.skip_ws();

            if self.s.peek() == Some('}') {
                return Ok(fields);
            }

            let (key, value) = self.field()?;

            self.skip_trivia();

            fields.insert(key, value);

            match self.s.peek() {
                Some(',') => self.comma()?,
                Some('}') => {
                    return Ok(fields);
                }
                _ => {
                    return Err(ParseError::new(
                        self.here(),
                        ParseErrorKind::Expected(Token::Comma),
                    ));
                }
            }
        }

        Err(ParseError::new(self.here(), ParseErrorKind::UnexpectedEof))
    }

    /// Eat an identifier.
    fn ident(&mut self) -> Result<&'s str, ParseError> {
        let idx = self.s.index();
        let is_start = self.s.peek().map(|c| is_id_start(c)).unwrap_or_default();

        if is_start {
            self.s.eat();
            self.s.eat_while(|c| is_id_continue(c));
            Ok(self.s.eaten_from(idx))
        } else {
            Err(ParseError::new(
                self.here(),
                ParseErrorKind::Expected(Token::Identifier),
            ))
        }
    }

    /// Eat an entry.
    fn entry(&mut self) -> Result<(), ParseError> {
        self.s.eat_assert('@');
        let entry_type = self.ident()?;
        self.skip_trivia();
        self.brace(true)?;
        self.skip_trivia();

        match entry_type.to_ascii_lowercase().as_str() {
            "string" => self.strings()?,
            "preamble" => self.preamble()?,
            _ => self.body(entry_type)?,
        }

        self.skip_trivia();
        self.brace(false)?;

        Ok(())
    }

    /// Eat the body of a strings entry.
    fn strings(&mut self) -> Result<(), ParseError> {
        let fields = self.fields()?;
        self.res.abbreviations.extend(fields);
        Ok(())
    }

    /// Eat the body of a preamble entry.
    fn preamble(&mut self) -> Result<(), ParseError> {
        let idx = self.s.index();
        self.string()?;
        let string = self.s.eaten_from(idx);

        if !self.res.preamble.is_empty() {
            self.res.preamble.push_str(" # ");
        }

        self.res.preamble.push_str(string);

        Ok(())
    }

    /// Eat the body of a entry.
    fn body(&mut self, kind: &'s str) -> Result<(), ParseError> {
        let key = self.ident()?;
        self.skip_ws();
        self.comma()?;

        self.skip_trivia();
        let fields = self.fields()?;

        self.res.entries.push(RawEntry { key, kind, fields });
        Ok(())
    }

    /// Return a span of the current position.
    fn here(&self) -> std::ops::Range<usize> {
        let pos = self.s.index();
        pos .. pos
    }
}

#[cfg(test)]
#[rustfmt::skip]
mod tests {
    use super::*;

    #[track_caller]
    fn test_prop(key: &str, value: &str) -> String {
        let test = format!("@article{{test, {}={}}}", key, value);
        let bt = RawBibliography::parse(&test);
        let article = &bt.entries[0];
        article.fields.get(key).expect("fail").to_string()
    }

    #[test]
    fn test_parse_article() {
        let file = "@article{haug2020,
            title = \"Great proceedings\\{\",
            year=2002,
            author={Haug, {Martin} and Haug, Gregor}}";

        let bt = RawBibliography::parse(file);
        let article = &bt.entries[0];

        assert_eq!(article.kind, "article");
        assert_eq!(article.fields.get("title"), Some(&"\"Great proceedings\\{\""));
        assert_eq!(article.fields.get("year"), Some(&"2002"));
        assert_eq!(article.fields.get("author"), Some(&"{Haug, {Martin} and Haug, Gregor}"));
    }

    #[test]
    fn test_resolve_string() {
        let bt = RawBibliography::parse("@string{BT = \"bibtex\"}");
        assert_eq!(bt.abbreviations.get("BT"), Some(&"\"bibtex\""));
    }

    #[test]
    fn test_escape() {
        assert_eq!(test_prop("author", "{Mister A\\}\"B\"}"), "{Mister A\\}\"B\"}");
    }
}
