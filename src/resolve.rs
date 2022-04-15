use std::collections::HashMap;

use unicode_normalization::char;

use crate::chunk::{Chunk, Chunks};
use crate::mechanics::is_verbatim_field;
use crate::raw::{Field, ParseError, ParseErrorKind, RawChunk, Token};
use crate::scanner::{is_id_continue, is_newline, Scanner};
use crate::types::get_month_for_abbr;
use crate::ChunksExt;

/// Fully parse a field, resolving abbreviations and LaTeX commands.
pub fn parse_field(
    key: &str,
    field: &Field,
    abbreviations: &HashMap<&str, Field<'_>>,
) -> Result<Chunks, ParseError> {
    let mut chunks = vec![];
    for e in field {
        match e {
            RawChunk::Abbreviation(s) => {
                chunks.extend(resolve_abbreviation(key, s, abbreviations)?);
            }
            RawChunk::Normal(s) => {
                chunks.extend(ContentParser::new(key, s).parse()?);
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
}

impl<'s> ContentParser<'s> {
    fn new(key: &'s str, field: &'s str) -> Self {
        Self {
            s: Scanner::new(field),
            verb_field: is_verbatim_field(key),
        }
    }

    fn parse(mut self) -> Result<Chunks, ParseError> {
        let mut depth = 0;
        let default_chunk = |depth| {
            if depth > 0 {
                Chunk::Verbatim(String::new())
            } else {
                Chunk::Normal(String::new())
            }
        };
        let mut current = default_chunk(depth);
        let mut res = vec![];

        loop {
            match self.s.peek() {
                Some('\\') => current.get_mut().push_str(&self.backslash()?),
                Some('$') => {
                    res.push(current);
                    current = default_chunk(depth);

                    res.push(self.math()?);
                }
                Some('{') => {
                    res.push(current);
                    depth += 1;
                    current = default_chunk(depth);

                    self.s.eat();
                }
                Some('}') => {
                    if depth == 0 {
                        let idx = self.s.index();
                        self.s.eat();
                        return Err(ParseError::new(
                            idx .. self.s.index(),
                            ParseErrorKind::Unexpected(Token::ClosingBrace),
                        ));
                    }

                    res.push(current);
                    depth -= 1;
                    current = default_chunk(depth);

                    self.s.eat();
                }
                Some(_) => current.get_mut().push(self.s.eat().unwrap()),
                None => break,
            }
        }

        if !current.get().is_empty() {
            res.push(current);
        }

        Ok(res)
    }

    fn backslash(&mut self) -> Result<String, ParseError> {
        self.s.eat_assert('\\');
        // TODO fix escaping for file field
        match self.s.peek() {
            Some(c) if is_escapable(c, self.verb_field) => {
                self.s.eat_assert(c);
                Ok(c.to_string())
            }
            _ if self.verb_field => {
                return Ok("\\".to_string());
            }
            Some(c) if !c.is_whitespace() && !c.is_control() => self.command(),
            Some(c) => Ok(format!("\\{}", c)),
            None => Err(ParseError::new(
                self.s.here(),
                ParseErrorKind::UnexpectedEof,
            )),
        }
    }

    fn command(&mut self) -> Result<String, ParseError> {
        let pos = self.s.index();
        let valid_start = self
            .s
            .peek()
            .map(|c| !c.is_whitespace() && !c.is_control() && !is_newline(c))
            .unwrap_or_default();
        if !valid_start {
            return Err(ParseError::new(
                pos .. self.s.index(),
                ParseErrorKind::MalformedCommand,
            ));
        }

        if !is_single_char_func(self.s.eat().unwrap()) {
            self.s.eat_while(|c| is_id_continue(c));
        }

        let command = self.s.eaten_from(pos);
        let ws = !self.s.eat_while(|c| c.is_whitespace()).is_empty();

        let arg = if self.s.peek() != Some('{')
            && command.chars().count() == 1
            && is_single_char_func(command.chars().next().unwrap())
        {
            let idx = self.s.index();
            self.s.eat();
            Some(self.s.eaten_from(idx).into())
        } else if !ws && self.s.eat_if('{') {
            let mut depth = 1;
            let idx = self.s.index();

            loop {
                self.s.eat_until(|c| c == '}' || c == '{');

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
                            self.s.here(),
                            ParseErrorKind::UnexpectedEof,
                        ));
                    }
                }
            }

            let brace = '}'.len_utf8();
            let arg = self.s.eaten_from(idx);

            let arg = ContentParser::new("", &arg[.. arg.len() - brace])
                .parse()?
                .format_verbatim();

            Some(arg)
        } else {
            None
        };

        Ok(execute_command(command, arg.as_deref()))
    }

    fn math(&mut self) -> Result<Chunk, ParseError> {
        self.s.eat_assert('$');
        let res = self.s.eat_until(|c| c == '$');

        if self.s.eof() {
            return Err(ParseError::new(
                self.s.here(),
                ParseErrorKind::UnexpectedEof,
            ));
        }

        self.s.eat();
        Ok(Chunk::Math(res.into()))
    }
}

/// Resolves `Chunk::Abbreviation` items to their respective string values.
fn resolve_abbreviation(
    key: &str,
    abbr: &str,
    map: &HashMap<&str, Field<'_>>,
) -> Result<Chunks, ParseError> {
    let fields = map.get(abbr).ok_or(ParseError::new(
        0 .. 0,
        ParseErrorKind::UnknownAbbreviation(abbr.into()),
    ));

    if fields.is_err() {
        if let Some(month) = get_month_for_abbr(abbr) {
            return Ok(vec![Chunk::Normal(month.0)]);
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

    // TODO dump unused arguments, reject unknown commands
}

/// Simplifies a chunk vector by collapsing neighboring Normal or Verbatim chunks.
fn flatten(chunks: &mut Chunks) {
    let mut i = 1;

    loop {
        if i >= chunks.len() {
            break;
        }

        let merge = match (&chunks[i - 1], &chunks[i]) {
            (Chunk::Normal(_), Chunk::Normal(_)) => true,
            (Chunk::Verbatim(_), Chunk::Verbatim(_)) => true,
            _ => false,
        };

        if merge {
            let redundant =
                std::mem::replace(&mut chunks[i], Chunk::Normal("".to_string()));
            chunks[i - 1].get_mut().push_str(redundant.get());
            chunks.remove(i);
        } else {
            i += 1;
        }
    }
}

/// Characters that can be escaped.
pub fn is_escapable(c: char, verb: bool) -> bool {
    match c {
        '{' | '}' | '\\' => true,
        '&' | '%' | '$' | '_' if !verb => true,
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

    use super::{parse_field, Chunk, RawChunk};

    fn N(s: &str) -> Chunk {
        Chunk::Normal(s.to_string())
    }
    fn V(s: &str) -> Chunk {
        Chunk::Verbatim(s.to_string())
    }
    fn M(s: &str) -> Chunk {
        Chunk::Math(s.to_string())
    }

    #[test]
    fn test_process() {
        let mut map = HashMap::new();
        map.insert("abc", vec![RawChunk::Normal("ABC")]);
        map.insert("hi", vec![RawChunk::Normal("hello")]);
        map.insert("you", vec![RawChunk::Normal("person")]);

        let field = vec![
            RawChunk::Abbreviation("abc"),
            RawChunk::Normal("good {TIMES}"),
            RawChunk::Abbreviation("hi"),
            RawChunk::Abbreviation("you"),
            RawChunk::Normal("last"),
        ];

        let res = parse_field("", &field, &map).unwrap();
        assert_eq!(res[0], N("ABCgood "));
        assert_eq!(res[1], V("TIMES"));
        assert_eq!(res[2], N("hellopersonlast"));
        assert_eq!(res.len(), 3);
    }

    #[test]
    fn test_resolve_commands_and_escape() {
        let field = vec![RawChunk::Normal("\\\"{A}ther und {\"\\LaTeX \"} {\\relax for you\\}}")];

        let res = parse_field("", &field, &HashMap::new()).unwrap();
        assert_eq!(res[0], N("Äther und "));
        assert_eq!(res[1], V("\"LaTeX\""));
        assert_eq!(res[2], N(" "));
        assert_eq!(res[3], V("\\relax for you}"));
        assert_eq!(res.len(), 4);

        let field = vec![RawChunk::Normal("M\\\"etal S\\= ound")];

        let res = parse_field("", &field, &HashMap::new()).unwrap();
        assert_eq!(res[0], N("Mëtal Sōund"));
    }

    #[test]
    fn test_math() {
        let field = vec![RawChunk::Normal("The $11^{th}$ International Conference on How To Make \\$\\$")];

        let res = parse_field("", &field, &HashMap::new()).unwrap();
        assert_eq!(res[0], N("The "));
        assert_eq!(res[1], M("11^{th}"));
        assert_eq!(res[2], N(" International Conference on How To Make $$"));
        assert_eq!(res.len(), 3);
    }

    #[test]
    fn test_commands() {
        let field = vec![RawChunk::Normal("Bose\\textendash{}Einstein")];

        let res = parse_field("", &field, &HashMap::new()).unwrap();
        assert_eq!(res[0], N("Bose–Einstein"));
    }
}
