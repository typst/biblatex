//! Low-level representation of a bibliography file.

use std::fmt;
use std::{collections::HashMap, vec};

use crate::scanner::{is_id_continue, is_id_start, Scanner};
use crate::{Spanned, TypeError};

pub type Field<'s> = Vec<Spanned<RawChunk<'s>>>;

/// A literal representation of a bibliography file, with abbreviations not yet
/// resolved.
#[derive(Debug, Clone)]
pub struct RawBibliography<'s> {
    /// TeX commands to be prepended to the document, only supported by BibTeX.
    pub preamble: String,
    /// The collection of citation keys and bibliography entries.
    pub entries: Vec<Spanned<RawEntry<'s>>>,
    /// A map of reusable abbreviations, only supported by BibTeX.
    pub abbreviations: HashMap<&'s str, Field<'s>>,
}

/// A raw extracted entry, with abbreviations not yet resolved.
#[derive(Debug, Clone)]
pub struct RawEntry<'s> {
    /// The citation key.
    pub key: &'s str,
    /// Denotes the type of bibliographic item (e.g. `article`).
    pub kind: &'s str,
    /// Maps from field names to their values.
    pub fields: HashMap<&'s str, Field<'s>>,
}

/// A literal representation of a bibliography entry field.
#[derive(Debug, Clone, PartialEq)]
pub enum RawChunk<'s> {
    /// A normal field value.
    Normal(&'s str),
    /// A field with strings and abbreviations.
    Abbreviation(&'s str),
}

impl<'s> RawBibliography<'s> {
    /// Parse a raw bibliography from a source string.
    pub fn parse(src: &'s str) -> Result<Self, ParseError> {
        BiblatexParser::new(src).parse()
    }
}

/// Backing struct for parsing a Bib(La)TeX file into a [`RawBibliography`].
struct BiblatexParser<'s> {
    s: Scanner<'s>,
    res: RawBibliography<'s>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ParseError {
    pub span: std::ops::Range<usize>,
    pub kind: ParseErrorKind,
}

impl ParseError {
    pub(crate) fn new(span: std::ops::Range<usize>, kind: ParseErrorKind) -> Self {
        Self { span, kind }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}-{}", self.kind, self.span.start, self.span.end)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParseErrorKind {
    UnexpectedEof,
    Unexpected(Token),
    Expected(Token),
    UnknownAbbreviation(String),
    MalformedCommand,
    DuplicateKey(String),
    TypeError(TypeError),
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Token {
    Identifier,
    OpeningBrace,
    ClosingBrace,
    Comma,
    QuotationMark,
    Equals,
    DecimalPoint,
}

impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::UnexpectedEof => write!(f, "unexpected end of file"),
            Self::Expected(token) => write!(f, "expected {}", token),
            Self::Unexpected(token) => write!(f, "unexpected {}", token),
            Self::UnknownAbbreviation(s) => write!(f, "unknown abbreviation {:?}", s),
            Self::MalformedCommand => write!(f, "malformed command"),
            Self::DuplicateKey(s) => write!(f, "duplicate key {:?}", s),
            Self::TypeError(e) => write!(f, "{}", e),
        }
    }
}

impl From<TypeError> for ParseError {
    fn from(e: TypeError) -> Self {
        Self::new(e.span.clone(), ParseErrorKind::TypeError(e))
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
            Self::Identifier => "identifier",
            Self::OpeningBrace => "opening brace",
            Self::ClosingBrace => "closing brace",
            Self::Comma => "comma",
            Self::QuotationMark => "double quote",
            Self::Equals => "equals",
            Self::DecimalPoint => "decimal point",
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
    pub fn parse(mut self) -> Result<RawBibliography<'s>, ParseError> {
        while !self.s.eof() {
            self.s.skip_trivia();
            match self.s.peek() {
                Some('@') => self.entry()?,
                Some(_) => {
                    self.s.eat();
                }
                None => break,
            }
        }

        Ok(self.res)
    }

    /// Eat a comma.
    fn comma(&mut self) -> Result<(), ParseError> {
        if !self.s.eat_if(',') {
            return Err(ParseError::new(
                self.s.here(),
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
                self.s.here(),
                ParseErrorKind::Expected(token),
            ))
        }
    }

    /// Eat a quote.
    fn quote(&mut self) -> Result<(), ParseError> {
        if !self.s.eat_if('"') {
            Err(ParseError::new(
                self.s.here(),
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
                self.s.here(),
                ParseErrorKind::Expected(Token::Equals),
            ))
        } else {
            Ok(())
        }
    }

    /// Eat a string.
    fn string(&mut self) -> Result<Spanned<&'s str>, ParseError> {
        self.quote()?;
        let idx = self.s.index();

        while let Some(c) = self.s.peek() {
            match c {
                '"' => {
                    let res = self.s.eaten_from(idx);
                    let span = idx .. self.s.index();
                    self.quote()?;
                    return Ok(Spanned::new(res, span));
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

        Err(ParseError::new(
            self.s.here(),
            ParseErrorKind::UnexpectedEof,
        ))
    }

    /// Eat a number.
    fn number(&mut self) -> Result<&'s str, ParseError> {
        let idx = self.s.index();
        let mut has_dot = false;

        while let Some(c) = self.s.peek() {
            let start = self.s.index();
            match c {
                '0' ..= '9' => {
                    self.s.eat();
                }
                '.' => {
                    if !has_dot {
                        self.s.eat();
                        has_dot = true;
                    } else {
                        return Err(ParseError::new(
                            start .. self.s.index(),
                            ParseErrorKind::Unexpected(Token::DecimalPoint),
                        ));
                    }
                }
                _ => {
                    return Ok(self.s.eaten_from(idx));
                }
            }
        }

        Err(ParseError::new(
            self.s.here(),
            ParseErrorKind::UnexpectedEof,
        ))
    }

    /// Eat a braced value.
    fn braced(&mut self) -> Result<Spanned<RawChunk<'s>>, ParseError> {
        self.brace(true)?;
        let idx = self.s.index();
        let mut braces = 0;

        while let Some(c) = self.s.peek() {
            match c {
                '{' => {
                    self.brace(true)?;
                    braces += 1;
                }
                '}' => {
                    let res = self.s.eaten_from(idx);
                    let span = idx .. self.s.index();
                    self.brace(false)?;
                    if braces == 0 {
                        return Ok(Spanned::new(RawChunk::Normal(res), span));
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

        Err(ParseError::new(
            self.s.here(),
            ParseErrorKind::UnexpectedEof,
        ))
    }

    /// Eat an element of an abbreviation.
    fn abbr_element(&mut self) -> Result<Spanned<RawChunk<'s>>, ParseError> {
        let start = self.s.index();
        let res = match self.s.peek() {
            Some(c) if is_id_start(c) => self.ident().map(|s| RawChunk::Abbreviation(s)),
            Some(c) if c.is_numeric() => self.number().map(|s| RawChunk::Normal(s)),
            _ => {
                return self
                    .string()
                    .map(|s| Spanned::new(RawChunk::Normal(s.v), s.span));
            }
        };

        res.map(|v| Spanned::new(v, start .. self.s.index()))
    }

    /// Eat an abbreviation field.
    fn abbr_field(&mut self) -> Result<Field<'s>, ParseError> {
        let mut elems = vec![];

        loop {
            elems.push(self.abbr_element()?);
            self.s.skip_ws();
            if !self.s.eat_if('#') {
                break;
            }
            self.s.skip_ws();
        }

        Ok(elems)
    }

    /// Eat a field.
    fn field(&mut self) -> Result<(&'s str, Field<'s>), ParseError> {
        let key = self.ident()?;
        self.s.skip_ws();
        self.equals()?;
        self.s.skip_ws();

        let value = match self.s.peek() {
            Some('{') => vec![self.braced()?],
            Some(_) => self.abbr_field()?,
            None => {
                return Err(ParseError::new(
                    self.s.here(),
                    ParseErrorKind::UnexpectedEof,
                ));
            }
        };

        self.s.skip_ws();

        Ok((key, value))
    }

    /// Eat fields.
    fn fields(&mut self) -> Result<HashMap<&'s str, Field<'s>>, ParseError> {
        let mut fields = HashMap::new();

        while !self.s.eof() {
            self.s.skip_ws();

            if self.s.peek() == Some('}') {
                return Ok(fields);
            }

            let (key, value) = self.field()?;

            self.s.skip_trivia();

            fields.insert(key, value);

            match self.s.peek() {
                Some(',') => self.comma()?,
                Some('}') => {
                    return Ok(fields);
                }
                _ => {
                    return Err(ParseError::new(
                        self.s.here(),
                        ParseErrorKind::Expected(Token::Comma),
                    ));
                }
            }
        }

        Err(ParseError::new(
            self.s.here(),
            ParseErrorKind::UnexpectedEof,
        ))
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
                self.s.here(),
                ParseErrorKind::Expected(Token::Identifier),
            ))
        }
    }

    /// Eat an entry.
    fn entry(&mut self) -> Result<(), ParseError> {
        let start = self.s.index();
        self.s.eat_assert('@');
        let entry_type = self.ident()?;
        self.s.skip_trivia();
        self.brace(true)?;
        self.s.skip_trivia();

        match entry_type.to_ascii_lowercase().as_str() {
            "string" => self.strings()?,
            "preamble" => self.preamble()?,
            _ => self.body(entry_type, start)?,
        }

        self.s.skip_trivia();
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
    fn body(&mut self, kind: &'s str, start: usize) -> Result<(), ParseError> {
        let key = self.ident()?;
        self.s.skip_ws();
        self.comma()?;

        self.s.skip_trivia();
        let fields = self.fields()?;

        self.res.entries.push(Spanned::new(
            RawEntry { key, kind, fields },
            start .. self.s.index(),
        ));
        Ok(())
    }
}

#[cfg(test)]
#[rustfmt::skip]
mod tests {
    use super::*;

    fn format(field: &Field<'_>) -> String {
        if field.len() == 1 {
            if let Some(RawChunk::Normal(s)) = field.first().map(|s| &s.v) {
                return format!("{{{}}}", s);
            }
        }

        let mut res = String::new();
        let mut first = true;

        for field in field {
            if !first {
                res.push_str(" # ");
            } else {
                first = false;
            }

            match field.v {
                RawChunk::Normal(s) => {
                    res.push('"');
                    res.push_str(s);
                    res.push('"');
                },
                RawChunk::Abbreviation(s) => res.push_str(s),
            }
        }

        res
    }

    #[track_caller]
    fn test_prop(key: &str, value: &str) -> String {
        let test = format!("@article{{test, {}={}}}", key, value);
        let bt = RawBibliography::parse(&test).unwrap();
        let article = &bt.entries[0];
        format(article.v.fields.get(key).expect("fail"))
    }

    #[test]
    fn test_parse_article() {
        let file = "@article{haug2020,
            title = \"Great proceedings\\{\",
            year=2002,
            author={Haug, {Martin} and Haug, Gregor}}";

        let bt = RawBibliography::parse(file).unwrap();
        let article = &bt.entries[0];

        assert_eq!(article.v.kind, "article");
        assert_eq!(format(article.v.fields.get("title").unwrap()), "{Great proceedings\\{}");
        assert_eq!(format(article.v.fields.get("year").unwrap()), "2002");
        assert_eq!(format(article.v.fields.get("author").unwrap()), "{Haug, {Martin} and Haug, Gregor}");
    }

    #[test]
    fn test_resolve_string() {
        let bt = RawBibliography::parse("@string{BT = \"bibtex\"}").unwrap();
        assert_eq!(bt.abbreviations.get("BT"), Some(&vec![Spanned::new(RawChunk::Normal("bibtex"), 14..20)]));
    }

    #[test]
    fn test_escape() {
        assert_eq!(test_prop("author", "{Mister A\\}\"B\"}"), "{Mister A\\}\"B\"}");
    }
}
