use std::collections::HashMap;

use unicode_normalization::char;

use crate::chunk::{Chunk, Chunks};
use crate::mechanics::is_verbatim_field;
use crate::raw::{is_id_continue, Field, ParseError, ParseErrorKind, RawChunk, Token};
use crate::types::get_month_for_abbr;
use crate::{ChunksExt, Span, Spanned};
use unscanny::Scanner;

/// Fully parse a field, resolving abbreviations and LaTeX commands.
pub fn parse_field(
    key: &str,
    field: &Field,
    abbreviations: &HashMap<&str, Field<'_>>,
) -> Result<Chunks, ParseError> {
    let mut chunks = vec![];
    for e in field {
        match e.v {
            RawChunk::Abbreviation(s) => {
                chunks.extend(resolve_abbreviation(
                    key,
                    s,
                    e.span.clone(),
                    abbreviations,
                )?);
            }
            RawChunk::Normal(s) => {
                chunks.extend(ContentParser::new(key, s, e.span.start).parse()?);
            }
        }
    }

    flatten(&mut chunks);
    Ok(chunks)
}

#[derive(Clone)]
struct ContentParser<'s> {
    s: Scanner<'s>,
    verb_field: bool,
    current_chunk: Chunk,
    result: Chunks,
    start: usize,
    offset: usize,
}

impl<'s> ContentParser<'s> {
    fn new(key: &'s str, field: &'s str, offset: usize) -> Self {
        Self {
            s: Scanner::new(field),
            verb_field: is_verbatim_field(key),
            current_chunk: Self::default_chunk(0),
            result: vec![],
            start: 0,
            offset,
        }
    }

    fn parse(self) -> Result<Chunks, ParseError> {
        let offset = self.offset;
        self.parse_impl()
            .map_err(|mut e| {
                e.span.start += offset;
                e.span.end += offset;
                e
            })
            .map(|mut chunks| {
                for chunk in &mut chunks {
                    chunk.span.start += offset;
                    chunk.span.end += offset;
                }

                chunks
            })
    }

    fn parse_impl(mut self) -> Result<Chunks, ParseError> {
        let mut depth = 0;

        self.current_chunk = Self::default_chunk(depth);

        while let Some(c) = self.s.peek() {
            match c {
                '\\' => {
                    let sequence = self.backslash()?;
                    self.current_chunk.get_mut().push_str(&sequence)
                }
                '$' => {
                    self.turnaround(depth);
                    let math = self.math()?;
                    self.result.push(math);
                }
                '{' => {
                    depth += 1;
                    self.turnaround(depth);
                    self.s.eat();
                    self.start += 1;
                }
                '}' => {
                    if depth == 0 {
                        let idx = self.s.cursor();
                        self.s.eat();
                        return Err(ParseError::new(
                            idx .. self.s.cursor(),
                            ParseErrorKind::Unexpected(Token::ClosingBrace),
                        ));
                    }

                    depth -= 1;
                    self.turnaround(depth);
                    self.start += 1;

                    self.s.eat();
                }
                _ => self.current_chunk.get_mut().push(self.s.eat().unwrap()),
            }
        }

        if !self.current_chunk.get().is_empty() {
            self.turnaround(depth);
        }

        Ok(self.result)
    }

    fn turnaround(&mut self, depth: usize) {
        self.result.push(Spanned::new(
            std::mem::replace(&mut self.current_chunk, Self::default_chunk(depth)),
            self.start .. self.s.cursor(),
        ));
        self.start = self.s.cursor();
    }

    fn backslash(&mut self) -> Result<String, ParseError> {
        self.eat_assert('\\');
        match self.s.peek() {
            Some(c) if is_escapable(c, self.verb_field, true) => {
                self.s.eat();
                Ok(c.to_string())
            }
            _ if self.verb_field => {
                return Ok("\\".to_string());
            }
            Some(c) if !c.is_whitespace() && !c.is_control() => self.command(),
            Some(c) => Ok(format!("\\{}", c)),
            None => Err(ParseError::new(self.here(), ParseErrorKind::UnexpectedEof)),
        }
    }

    fn command(&mut self) -> Result<String, ParseError> {
        let pos = self.s.cursor();
        let valid_start = self
            .s
            .peek()
            .map(|c| !c.is_whitespace() && !c.is_control())
            .unwrap_or_default();
        if !valid_start {
            return Err(ParseError::new(
                pos .. self.s.cursor(),
                ParseErrorKind::MalformedCommand,
            ));
        }

        if !is_single_char_func(self.s.eat().unwrap()) {
            self.s.eat_while(is_id_continue);
        }

        let command = self.s.from(pos);
        let ws = !self.s.eat_whitespace().is_empty();

        let arg = if self.s.peek() != Some('{')
            && command.chars().count() == 1
            && is_single_char_func(command.chars().next().unwrap())
        {
            let idx = self.s.cursor();
            self.s.eat();
            Some(self.s.from(idx).into())
        } else if !ws && self.s.eat_if('{') {
            let mut depth = 1;
            let idx = self.s.cursor();

            loop {
                self.s.eat_until(['{', '}']);

                match self.s.eat() {
                    Some('{') => {
                        depth += 1;
                    }
                    Some('}') => {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                    Some(_) => unreachable!(),
                    None => {
                        return Err(ParseError::new(
                            self.here(),
                            ParseErrorKind::UnexpectedEof,
                        ));
                    }
                }
            }

            let brace = '}'.len_utf8();
            let arg = self.s.from(idx);

            let arg = ContentParser::new("", &arg[.. arg.len() - brace], idx)
                .parse()?
                .format_verbatim();

            Some(arg)
        } else {
            None
        };

        Ok(execute_command(command, arg.as_deref()))
    }

    fn math(&mut self) -> Result<Spanned<Chunk>, ParseError> {
        self.eat_assert('$');
        let idx = self.s.cursor();
        let res = self.s.eat_until(|c| c == '$');
        let span = idx .. self.s.cursor();

        if self.s.done() {
            return Err(ParseError::new(self.here(), ParseErrorKind::UnexpectedEof));
        }

        self.s.eat();
        self.start = self.s.cursor();
        Ok(Spanned::new(Chunk::Math(res.into()), span))
    }

    #[track_caller]
    fn eat_assert(&mut self, c: char) {
        if self.s.eat() != Some(c) {
            panic!("assertion failed: expected '{}'", c);
        }
    }

    fn here(&self) -> Span {
        self.s.cursor() .. self.s.cursor()
    }

    fn default_chunk(depth: usize) -> Chunk {
        if depth > 0 {
            Chunk::Verbatim(String::new())
        } else {
            Chunk::Normal(String::new())
        }
    }
}

/// Resolves `Chunk::Abbreviation` items to their respective string values.
fn resolve_abbreviation(
    key: &str,
    abbr: &str,
    span: Span,
    map: &HashMap<&str, Field<'_>>,
) -> Result<Chunks, ParseError> {
    let fields = map.get(abbr).ok_or(ParseError::new(
        span.clone(),
        ParseErrorKind::UnknownAbbreviation(abbr.into()),
    ));

    if fields.is_err() {
        if let Some(month) = get_month_for_abbr(abbr) {
            return Ok(vec![Spanned::new(Chunk::Normal(month.0.to_string()), span)]);
        }
    }

    parse_field(key, fields?, map)
}

/// Best-effort evaluation of LaTeX commands with a focus on diacritics.
/// Will dump the command arguments if evaluation not possible.
/// Nested commands are not supported.
fn execute_command(command: &str, arg: Option<&str>) -> String {
    fn last_char_combine(v: Option<&str>, combine: char) -> String {
        if let Some(v) = v {
            if v.is_empty() {
                combine.into()
            } else {
                let mut chars = v.chars();

                // Account for legacy TeX behavior of requiring an uncapped i or
                // j to add another diacritic.
                let last = match chars.next_back().unwrap() {
                    'ı' => 'i',
                    'ȷ' => 'j',
                    c => c,
                };

                let combined = char::compose(last, combine).unwrap_or(last);
                let mut res = chars.as_str().to_string();
                res.push(combined);

                res
            }
        } else {
            combine.into()
        }
    }

    match command {
        "LaTeX" => "LaTeX".to_string(),
        "TeX" => "TeX".to_string(),
        "textendash" => "–".to_string(),
        "textemdash" => "—".to_string(),
        "aa" => "å".to_string(),
        "AA" => "Å".to_string(),
        "l" => "ł".to_string(),
        "L" => "Ł".to_string(),
        "i" => "ı".to_string(),
        "oe" => "œ".to_string(),
        "OE" => "Œ".to_string(),
        "ae" => "æ".to_string(),
        "AE" => "Æ".to_string(),
        "o" if arg.is_none() => "ø".to_string(),
        "O" => "Ø".to_string(),
        "ss" => "ß".to_string(),
        "SS" => "ẞ".to_string(),
        "`" => last_char_combine(arg, '\u{300}'),
        "´" => last_char_combine(arg, '\u{301}'),
        "'" => last_char_combine(arg, '\u{301}'),
        "^" => last_char_combine(arg, '\u{302}'),
        "~" => last_char_combine(arg, '\u{303}'),
        "=" => last_char_combine(arg, '\u{304}'),
        "u" => last_char_combine(arg, '\u{306}'),
        "." => last_char_combine(arg, '\u{307}'),
        "\"" => last_char_combine(arg, '\u{308}'),
        "r" => last_char_combine(arg, '\u{30A}'),
        "H" => last_char_combine(arg, '\u{30B}'),
        "v" => last_char_combine(arg, '\u{30C}'),
        "d" => last_char_combine(arg, '\u{323}'),
        "c" => last_char_combine(arg, '\u{327}'),
        "k" => last_char_combine(arg, '\u{328}'),
        "b" => last_char_combine(arg, '\u{332}'),
        "o" => last_char_combine(arg, '\u{338}'),
        _ => {
            if let Some(arg) = arg {
                format!("\\{}{{{}}}", command, arg)
            } else {
                format!("\\{} ", command)
            }
        }
    }
}

/// Simplifies a chunk vector by collapsing neighboring Normal or Verbatim chunks.
fn flatten(chunks: &mut Chunks) {
    let mut i = 1;

    loop {
        if i >= chunks.len() {
            break;
        }

        let merge = match (&chunks[i - 1].v, &chunks[i].v) {
            (Chunk::Normal(_), Chunk::Normal(_)) => true,
            (Chunk::Verbatim(_), Chunk::Verbatim(_)) => true,
            _ => false,
        };

        if merge {
            let redundant = std::mem::replace(
                &mut chunks[i],
                Spanned::new(Chunk::Normal("".to_string()), 0 .. 0),
            );
            chunks[i - 1].v.get_mut().push_str(redundant.v.get());
            chunks[i - 1].span.end = redundant.span.end;
            chunks.remove(i);
        } else {
            i += 1;
        }
    }
}

/// Characters that can be escaped.
///
/// In read mode (`read_char = true`), colons are also converted to an unescaped string to keep
/// compatiblity with Zotero. Zotero escapes colons when exporting verbatim fields. This crate
/// doesn't escape colons when exporting.
pub fn is_escapable(c: char, verb: bool, read_char: bool) -> bool {
    match c {
        '{' | '}' | '\\' => true,
        '&' | '%' | '$' | '_' if !verb => true,
        ':' if read_char || !verb => true,
        _ => false,
    }
}

/// Characters that are the name of a single-char command
/// that automatically terminates.
fn is_single_char_func(c: char) -> bool {
    match c {
        '"' | '´' | '`' | '\'' | '^' | '~' | '=' | '.' | '\\' => true,
        _ => false,
    }
}

#[cfg(test)]
#[allow(non_snake_case)]
#[rustfmt::skip]
mod tests {
    use std::collections::HashMap;

    use super::{parse_field, Chunk, RawChunk, Spanned};

    fn N(s: &str) -> Chunk {
        Chunk::Normal(s.to_string())
    }
    fn V(s: &str) -> Chunk {
        Chunk::Verbatim(s.to_string())
    }
    fn M(s: &str) -> Chunk {
        Chunk::Math(s.to_string())
    }

    fn z(c: RawChunk) -> Spanned<RawChunk> {
        Spanned::new(c, 0 .. 0)
    }

    #[test]
    fn test_process() {
        let mut map = HashMap::new();
        map.insert("abc", vec![z(RawChunk::Normal("ABC"))]);
        map.insert("hi", vec![z(RawChunk::Normal("hello"))]);
        map.insert("you", vec![z(RawChunk::Normal("person"))]);

        let field = vec![
            z(RawChunk::Abbreviation("abc")),
            z(RawChunk::Normal("good {TIMES}")),
            z(RawChunk::Abbreviation("hi")),
            z(RawChunk::Abbreviation("you")),
            z(RawChunk::Normal("last")),
        ];

        let res = parse_field("", &field, &map).unwrap();
        assert_eq!(res[0].v, N("ABCgood "));
        assert_eq!(res[1].v, V("TIMES"));
        assert_eq!(res[2].v, N("hellopersonlast"));
        assert_eq!(res.len(), 3);
    }

    #[test]
    fn test_resolve_commands_and_escape() {
        let field = vec![z(RawChunk::Normal("\\\"{A}ther und {\"\\LaTeX \"} {\\relax for you\\}}"))];

        let res = parse_field("", &field, &HashMap::new()).unwrap();
        assert_eq!(res[0].v, N("Äther und "));
        assert_eq!(res[1].v, V("\"LaTeX\""));
        assert_eq!(res[2].v, N(" "));
        assert_eq!(res[3].v, V("\\relax for you}"));
        assert_eq!(res.len(), 4);

        let field = vec![z(RawChunk::Normal("M\\\"etal S\\= ound"))];

        let res = parse_field("", &field, &HashMap::new()).unwrap();
        assert_eq!(res[0].v, N("Mëtal Sōund"));
    }

    #[test]
    fn test_math() {
        let field = vec![z(RawChunk::Normal("The $11^{th}$ International Conference on How To Make \\$\\$"))];

        let res = parse_field("", &field, &HashMap::new()).unwrap();
        assert_eq!(res[0].v, N("The "));
        assert_eq!(res[1].v, M("11^{th}"));
        assert_eq!(res[2].v, N(" International Conference on How To Make $$"));
        assert_eq!(res.len(), 3);
    }

    #[test]
    fn test_commands() {
        let field = vec![z(RawChunk::Normal("Bose\\textendash{}Einstein"))];

        let res = parse_field("", &field, &HashMap::new()).unwrap();
        assert_eq!(res[0].v, N("Bose–Einstein"));
    }
}
