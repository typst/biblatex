//! Low-level representation of a bibliography file.

use std::fmt;

use crate::{Span, Spanned, TypeErrorKind};

use unscanny::Scanner;

/// The content of a field or abbreviation.
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
    pub abbreviations: Vec<Pair<'s>>,
}

/// A raw extracted entry, with abbreviations not yet resolved.
#[derive(Debug, Clone)]
pub struct RawEntry<'s> {
    /// The citation key.
    pub key: Spanned<&'s str>,
    /// Denotes the type of bibliographic item (e.g., `article`).
    pub kind: Spanned<&'s str>,
    /// Maps from field names to their values.
    pub fields: Vec<Pair<'s>>,
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

/// An error that might occur during initial parsing of the bibliography.
#[derive(Debug, Clone, PartialEq)]
pub struct ParseError {
    /// Where in the source the error occurred.
    pub span: std::ops::Range<usize>,
    /// What kind of error occurred.
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

/// Error conditions that might occur during initial parsing of the
/// bibliography.
///
/// Also see [`ParseError`].
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum ParseErrorKind {
    /// The file ended prematurely.
    UnexpectedEof,
    /// An unexpected token was encountered.
    Unexpected(Token),
    /// A token was expected, but not found.
    Expected(Token),
    /// A field contained an abbreviation that was not defined.
    UnknownAbbreviation(String),
    /// A TeX command was malformed.
    MalformedCommand,
    /// A duplicate citation key was found.
    DuplicateKey(String),
    /// A type error occurred while trying to resolve cross-references.
    ResolutionError(TypeErrorKind),
}

/// A token that can be encountered during parsing.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Token {
    /// An identifier for a field key, citation type, abbreviation, or citation
    /// key.
    Identifier,
    /// An opening brace: `{`.
    OpeningBrace,
    /// A closing brace: `}`.
    ClosingBrace,
    /// A comma: `,`.
    Comma,
    /// A quotation mark: `"`.
    QuotationMark,
    /// An equals sign: `=`.
    Equals,
    /// A decimal point: `.`.
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
            Self::ResolutionError(e) => {
                write!(f, "type error occurred during crossref resolution: {}", e)
            }
        }
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
                entries: Vec::new(),
                abbreviations: Vec::new(),
            },
        }
    }

    /// Parses the file, consuming the parser in the process.
    pub fn parse(mut self) -> Result<RawBibliography<'s>, ParseError> {
        while !self.s.done() {
            self.s.eat_whitespace();
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
                self.here(),
                ParseErrorKind::Expected(Token::Comma),
            ));
        }

        Ok(())
    }

    /// Eat a delimiter.
    fn brace(&mut self, open: bool) -> Result<(), ParseError> {
        let (brace, token) =
            if open { ('{', Token::OpeningBrace) } else { ('}', Token::ClosingBrace) };

        let peeked = self.s.peek();

        if peeked == Some(brace) || peeked == Some('\"') {
            self.s.eat();
            Ok(())
        } else {
            Err(ParseError::new(self.here(), ParseErrorKind::Expected(token)))
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
            Err(ParseError::new(self.here(), ParseErrorKind::Expected(Token::Equals)))
        } else {
            Ok(())
        }
    }

    /// Eat a string.
    fn string(&mut self) -> Result<Spanned<&'s str>, ParseError> {
        self.quote()?;
        let idx = self.s.cursor();

        while let Some(c) = self.s.peek() {
            match c {
                '"' => {
                    let res = self.s.from(idx);
                    let span = idx..self.s.cursor();
                    self.quote()?;
                    return Ok(Spanned::new(res, span));
                }
                '\\' => {
                    self.s.eat();
                    self.s.eat();
                }
                _ => {
                    self.s.eat();
                }
            }
        }

        Err(ParseError::new(self.here(), ParseErrorKind::UnexpectedEof))
    }

    /// Eat a number.
    fn number(&mut self) -> Result<&'s str, ParseError> {
        let idx = self.s.cursor();
        let mut has_dot = false;

        while let Some(c) = self.s.peek() {
            let start = self.s.cursor();
            match c {
                '0'..='9' => {
                    self.s.eat();
                }
                '.' => {
                    if !has_dot {
                        self.s.eat();
                        has_dot = true;
                    } else {
                        return Err(ParseError::new(
                            start..self.s.cursor(),
                            ParseErrorKind::Unexpected(Token::DecimalPoint),
                        ));
                    }
                }
                _ => {
                    return Ok(self.s.from(idx));
                }
            }
        }

        Err(ParseError::new(self.here(), ParseErrorKind::UnexpectedEof))
    }

    /// Eat a braced value.
    fn braced(&mut self) -> Result<Spanned<RawChunk<'s>>, ParseError> {
        self.brace(true)?;
        let idx = self.s.cursor();
        let mut braces = 0;

        while let Some(c) = self.s.peek() {
            match c {
                '{' => {
                    self.brace(true)?;
                    braces += 1;
                }
                '}' => {
                    let res = self.s.from(idx);
                    let span = idx..self.s.cursor();
                    self.brace(false)?;
                    if braces == 0 {
                        return Ok(Spanned::new(RawChunk::Normal(res), span));
                    }
                    braces -= 1;
                }
                '\\' => {
                    self.s.eat();
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
    fn abbr_element(&mut self) -> Result<Spanned<RawChunk<'s>>, ParseError> {
        let start = self.s.cursor();
        let res = match self.s.peek() {
            Some(c) if c.is_ascii_digit() => self.number().map(RawChunk::Normal),
            Some(c) if is_id_start(c) => {
                self.ident().map(|s| RawChunk::Abbreviation(s.v))
            }
            _ => {
                return self.single_field();
            }
        };

        res.map(|v| Spanned::new(v, start..self.s.cursor()))
    }

    /// Eat an abbreviation field.
    fn abbr_field(&mut self) -> Result<Spanned<Field<'s>>, ParseError> {
        let start = self.s.cursor();
        let mut elems = vec![];

        loop {
            elems.push(self.abbr_element()?);
            self.s.eat_whitespace();
            if !self.s.eat_if('#') {
                break;
            }
            self.s.eat_whitespace();
        }

        Ok(Spanned::new(elems, start..self.s.cursor()))
    }

    /// Eat a field.
    fn field(&mut self) -> Result<(Spanned<&'s str>, Spanned<Field<'s>>), ParseError> {
        let key = self.ident()?;
        self.s.eat_whitespace();
        self.equals()?;
        self.s.eat_whitespace();

        let value = self.abbr_field()?;

        self.s.eat_whitespace();

        Ok((key, value))
    }

    fn single_field(&mut self) -> Result<Spanned<RawChunk<'s>>, ParseError> {
        match self.s.peek() {
            Some('{') => self.braced(),
            Some('"') => {
                self.string().map(|s| Spanned::new(RawChunk::Normal(s.v), s.span))
            }
            _ => Err(ParseError::new(self.here(), ParseErrorKind::UnexpectedEof)),
        }
    }

    /// Eat fields.
    fn fields(&mut self) -> Result<Vec<Pair<'s>>, ParseError> {
        let mut fields = Vec::new();

        while !self.s.done() {
            self.s.eat_whitespace();

            if self.s.peek() == Some('}') {
                return Ok(fields);
            }

            let (key, value) = self.field()?;

            self.s.eat_whitespace();

            fields.push(Pair::new(key, value));

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

    /// Eat an entry key.
    fn key(&mut self) -> Result<Spanned<&'s str>, ParseError> {
        let idx = self.s.cursor();
        self.s.eat_while(is_key);

        Ok(Spanned::new(self.s.from(idx), idx..self.s.cursor()))
    }

    /// Eat an identifier.
    fn ident(&mut self) -> Result<Spanned<&'s str>, ParseError> {
        let idx = self.s.cursor();
        let is_start = self.s.peek().map(is_id_start).unwrap_or_default();

        if is_start {
            self.s.eat();
            self.s.eat_while(is_id_continue);
            Ok(Spanned::new(self.s.from(idx), idx..self.s.cursor()))
        } else {
            Err(ParseError::new(self.here(), ParseErrorKind::Expected(Token::Identifier)))
        }
    }

    /// Eat an entry.
    fn entry(&mut self) -> Result<(), ParseError> {
        let start = self.s.cursor();
        if self.s.eat() != Some('@') {
            panic!("must not call entry when not at an '@'");
        }

        let entry_type = self.ident()?;
        self.s.eat_whitespace();
        self.brace(true)?;
        self.s.eat_whitespace();

        match entry_type.v.to_ascii_lowercase().as_str() {
            "string" => self.strings()?,
            "preamble" => self.preamble()?,
            "comment" => {
                self.s.eat_until('}');
            }
            _ => self.body(entry_type, start)?,
        }

        self.s.eat_whitespace();
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
        let idx = self.s.cursor();
        self.string()?;
        let string = self.s.from(idx);

        if !self.res.preamble.is_empty() {
            self.res.preamble.push_str(" # ");
        }

        self.res.preamble.push_str(string);

        Ok(())
    }

    /// Eat the body of an entry.
    fn body(&mut self, kind: Spanned<&'s str>, start: usize) -> Result<(), ParseError> {
        let key = self.key()?;
        self.s.eat_whitespace();
        self.comma()?;

        self.s.eat_whitespace();
        let fields = self.fields()?;

        self.res
            .entries
            .push(Spanned::new(RawEntry { key, kind, fields }, start..self.s.cursor()));
        Ok(())
    }

    fn here(&self) -> Span {
        self.s.cursor()..self.s.cursor()
    }
}

/// The keys for fields and their values.
#[derive(Debug, Clone)]
pub struct Pair<'s> {
    /// The key.
    pub key: Spanned<&'s str>,
    /// The value.
    pub value: Spanned<Field<'s>>,
}

impl<'s> Pair<'s> {
    /// Constructs a new key-value pair.
    pub fn new(key: Spanned<&'s str>, value: Spanned<Field<'s>>) -> Self {
        Self { key, value }
    }
}

/// Whether a character is allowed in an entry key
#[inline]
pub fn is_key(c: char) -> bool {
    !matches!(c, ',' | '}') && !c.is_control() && !c.is_whitespace()
}

/// Whether a character can start an identifier.
#[inline]
pub fn is_id_start(c: char) -> bool {
    !matches!(c, ':' | '<' | '-' | '>') && is_id_continue(c)
}

/// Whether a character can continue an identifier.
#[inline]
pub fn is_id_continue(c: char) -> bool {
    !matches!(
        c,
        '@' | '{' | '}' | '"' | '#' | '\'' | '(' | ')' | ',' | '=' | '%' | '\\' | '~'
    ) && !c.is_control()
        && !c.is_whitespace()
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
        format(&article.v.fields[0].value.v)
    }

    #[test]
    fn test_entry_key() {
        let file = "@article{!\"#$%&'()*+-./123:;<=>?@ABC[\\]^_`abc{|~,}";
        let bt = RawBibliography::parse(file).unwrap();
        let article = &bt.entries[0];
        assert_eq!(article.v.key.v, "!\"#$%&'()*+-./123:;<=>?@ABC[\\]^_`abc{|~");
    }

    #[test]
    fn test_empty_entry_key() {
        let file = "@article{,}";
        let bt = RawBibliography::parse(file).unwrap();
        let article = &bt.entries[0];
        assert_eq!(article.v.key.v, "");
    }

    #[test]
    fn test_parse_article() {
        let file = "@article{haug2020,
            title = \"Great proceedings\\{\",
            year=2002,
            author={Haug, {Martin} and Haug, Gregor}}";

        let bt = RawBibliography::parse(file).unwrap();
        let article = &bt.entries[0];

        assert_eq!(article.v.kind.v, "article");

        assert_eq!(article.v.fields[0].key.v, "title");
        assert_eq!(article.v.fields[1].key.v, "year");
        assert_eq!(article.v.fields[2].key.v, "author");
        assert_eq!(format(&article.v.fields[0].value.v), "{Great proceedings\\{}");
        assert_eq!(format(&article.v.fields[1].value.v), "{2002}");
        assert_eq!(format(&article.v.fields[2].value.v), "{Haug, {Martin} and Haug, Gregor}");
    }

    #[test]
    fn test_resolve_string() {
        let bt = RawBibliography::parse("@string{BT = \"bibtex\"}").unwrap();
        assert_eq!(bt.abbreviations[0].key.v, "BT");
        assert_eq!(&bt.abbreviations[0].value.v, &vec![Spanned::new(RawChunk::Normal("bibtex"), 14..20)]);
    }

    #[test]
    fn test_escape() {
        assert_eq!(test_prop("author", "{Mister A\\}\"B\"}"), "{Mister A\\}\"B\"}");
    }

    #[test]
    fn test_abbr() {
        assert_eq!(test_prop("author", "dec # {~12}"), "dec # \"~12\"");
    }
}
