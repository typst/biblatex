use crate::resolve::is_escapable;
use crate::types::Type;
use crate::{Span, Spanned, TypeError};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A vector of chunks.
pub type Chunks = Vec<Spanned<Chunk>>;

/// A slice of chunks.
pub type ChunksRef<'a> = &'a [Spanned<Chunk>];

/// Represents one part of a field value.
#[derive(Debug, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Chunk {
    /// Normal values within quotes or single braces subject to
    /// capitalization formatting.
    Normal(String),
    /// Values nested in braces that are to be printed like specified
    /// in the file. Escapes keywords.
    ///
    /// Example: `"Inside {NASA}"` or `{Memes are {gReAT}}`.
    Verbatim(String),
    /// Values nested in dollar signs.
    Math(String),
}

impl Chunk {
    /// Get the string contained in the chunk.
    pub fn get(&self) -> &str {
        match self {
            Chunk::Normal(s) => s,
            Chunk::Verbatim(s) => s,
            Chunk::Math(s) => s,
        }
    }

    /// Get the string contained in the chunk and whether it is verbatim.
    fn get_and_verb(&self) -> (&str, bool) {
        match self {
            Chunk::Normal(s) => (s, false),
            Chunk::Verbatim(s) => (s, true),
            Chunk::Math(s) => (s, false),
        }
    }

    /// Mutably get the string contained in the chunk.
    pub fn get_mut(&mut self) -> &mut String {
        match self {
            Chunk::Normal(s) => s,
            Chunk::Verbatim(s) => s,
            Chunk::Math(s) => s,
        }
    }

    /// Get the string contained in the chunk with the characters escaped.
    ///
    /// There is no difference for BibTeX and BibLaTeX here, so there is only one function applicable to both.
    ///
    /// The `is_verbatim` argument indicates whether this string is intended for
    /// a verbatim field like `file` with limited escapes.
    pub fn to_biblatex_string(&self, is_verbatim: bool) -> String {
        let mut s = String::new();
        for c in self.get().chars() {
            if is_escapable(c, is_verbatim, false) {
                s.push('\\');
            }
            s.push(c);
        }
        s
    }
}

/// Additional methods for chunk slices.
pub trait ChunksExt {
    /// Parse the chunks into a type.
    fn parse<T: Type>(&self) -> Result<T, TypeError>;

    /// Format the chunks in sentence case.
    fn format_sentence(&self) -> String;

    /// Format the chunks verbatim.
    fn format_verbatim(&self) -> String;

    /// Output a span for all chunks in the collection.
    fn span(&self) -> Span;

    /// Serialize the chunks into a BibLaTeX string.
    ///
    /// There is no difference for BibTeX and BibLaTeX here, so there is only one function applicable to both.
    fn to_biblatex_string(&self, is_verbatim: bool) -> String;
}

impl ChunksExt for [Spanned<Chunk>] {
    fn parse<T: Type>(&self) -> Result<T, TypeError> {
        T::from_chunks(self)
    }

    fn format_sentence(&self) -> String {
        let mut out = String::new();
        let mut first = true;
        let mut prev_was_whitespace = false;

        for val in self {
            match &val.v {
                Chunk::Normal(s) => {
                    for mut c in s.chars() {
                        if c == '\n' || c == '\r' {
                            if prev_was_whitespace {
                                continue;
                            } else {
                                c = ' ';
                            }
                        }

                        if first {
                            out.extend(c.to_uppercase());
                        } else {
                            out.extend(c.to_lowercase());
                        }
                        first = false;
                        prev_was_whitespace = c.is_whitespace();
                    }
                }
                Chunk::Verbatim(s) => {
                    out.push_str(s);
                    prev_was_whitespace =
                        s.chars().last().map(char::is_whitespace).unwrap_or(false);
                }
                Chunk::Math(s) => {
                    out.push('$');
                    out += s;
                    out.push('$');
                }
            }

            first = false;
        }

        out
    }

    fn format_verbatim(&self) -> String {
        let mut out = String::new();
        let mut prev_was_whitespace = false;

        for val in self {
            match &val.v {
                Chunk::Normal(s) => {
                    for mut c in s.chars() {
                        if c == '\n' || c == '\r' {
                            if prev_was_whitespace {
                                continue;
                            } else {
                                c = ' ';
                            }
                        }

                        out.push(c);
                        prev_was_whitespace = c.is_whitespace();
                    }
                }
                Chunk::Verbatim(s) => {
                    out += s;
                    prev_was_whitespace =
                        s.chars().last().map(char::is_whitespace).unwrap_or(false);
                }
                Chunk::Math(s) => {
                    out.push('$');
                    out += s;
                    out.push('$');
                }
            }
        }

        out
    }

    fn span(&self) -> Span {
        let start = self.first().map(|c| c.span.start).unwrap_or(0);
        let end = self.last().map(|c| c.span.end).unwrap_or(start);
        start..end
    }

    fn to_biblatex_string(&self, is_verbatim: bool) -> String {
        let mut res = String::new();
        res.push('{');
        let mut extra_brace = false;

        for chunk in self.iter() {
            match &chunk.v {
                Chunk::Verbatim(_) if !extra_brace => {
                    res.push('{');
                    extra_brace = true;
                }
                Chunk::Normal(_) if extra_brace => {
                    res.push('}');
                    extra_brace = false;
                }
                Chunk::Math(_) => {
                    res.push('$');
                }
                _ => {}
            }

            res.push_str(&chunk.v.to_biblatex_string(is_verbatim));

            if let Chunk::Math(_) = &chunk.v {
                res.push('$');
            }
        }

        for _ in 0..if extra_brace { 2 } else { 1 } {
            res.push('}');
        }

        res
    }
}

/// An iterator over the characters in each chunk, indicating whether they are
/// verbatim or not. Chunk types other than `Normal` or `Verbatim` are omitted.
pub(crate) fn chunk_chars(chunks: ChunksRef) -> impl Iterator<Item = (char, bool)> + '_ {
    chunks.iter().flat_map(|chunk| {
        let (s, verbatim) = chunk.v.get_and_verb();

        s.chars().map(move |c| (c, verbatim))
    })
}

/// Combines the chunks, interlacing with the separator.
pub(crate) fn join_chunk_list(chunks: ChunksRef, sep: &str) -> Chunks {
    let mut res = vec![];
    let mut first = true;

    for chunk in chunks {
        if first {
            first = false;
        } else {
            res.push(Spanned::new(
                Chunk::Normal(sep.to_string()),
                chunk.span.start..chunk.span.start,
            ));
        }

        res.push(chunk.clone());
    }

    res
}

/// Splits chunk vectors that are a token lists as defined per the
/// [BibLaTeX Manual][manual] p. 16 along occurrences of the keyword.
///
/// [manual]: http://ctan.ebinger.cc/tex-archive/macros/latex/contrib/biblatex/doc/biblatex.pdf
pub(crate) fn split_token_lists(vals: ChunksRef, keyword: &str) -> Vec<Chunks> {
    let mut out = vec![];
    let mut latest = vec![];

    for val in vals {
        if let Chunk::Normal(s) = &val.v {
            let mut target = s.as_str();
            let mut start = val.span.start;

            while let Some(pos) = target.find(keyword) {
                let first = target[..pos].trim_end();
                latest.push(Spanned::new(
                    Chunk::Normal(first.to_string()),
                    start..start + pos,
                ));
                out.push(std::mem::take(&mut latest));

                target = target[pos + keyword.len()..].trim_start();
                start += pos + keyword.len();
            }

            latest.push(Spanned::new(
                Chunk::Normal(target.to_string()),
                start..val.span.end,
            ));
        } else {
            latest.push(val.clone());
        }
    }

    out.push(latest);
    out
}

/// Split the token list based on a keyword surrounded by whitespace
///
/// For Normal Chunks,
/// - The leading/trailing keyword is not considered as a valid split
/// (regardless of whether the keyword is preceded/followed by some
/// whitespace).
/// - If there are consecutive keywords, the characters between two consecutive
/// keywords (whether only whitespace or not) will be considered as a valid
/// split.
pub(crate) fn split_token_lists_with_kw(vals: ChunksRef, keyword: &str) -> Vec<Chunks> {
    let mut out = vec![];
    let mut latest = vec![];

    // Trim the beginning and the end of the parsed field
    let sanitize_latest = |latest: &mut Vec<Spanned<Chunk>>| {
        if latest.is_empty() {
            return;
        }

        let mut diff = 0;
        if let Chunk::Normal(s) = &mut latest[0].v {
            diff = s.len() - s.trim_start().len();
            s.drain(0..diff);
        }
        if !latest[0].is_detached() {
            latest[0].span.start += diff;
        }

        let mut new_len = 0;
        let end = latest.len() - 1;
        if let Chunk::Normal(s) = &mut latest[end].v {
            new_len = s.trim_end().len();
            s.truncate(new_len);
        }
        if !latest[end].is_detached() {
            latest[end].span.end = latest[end].span.start + new_len;
        }
    };

    for (chunk_idx, chunk) in vals.iter().enumerate() {
        if let Chunk::Normal(s) = &chunk.v {
            let mut start = chunk.span.start;

            // If the first chunk is normal -> leading keyword
            let s = if chunk_idx == 0 {
                let new_s = s.trim_start();
                if !chunk.is_detached() {
                    // Offset the span start by the number of characters trimmed
                    start = chunk.span.start + s.len() - new_s.len();
                }
                new_s
            } else {
                s
            };

            // If the last chunk is normal -> trailing keyword
            let s = if chunk_idx == vals.len() - 1 { s.trim_end() } else { s };

            let mut splits = s.split(keyword);
            // guaranteed to have a value
            let mut prev = splits.next().unwrap();

            let mut cur = String::new();

            for split in splits {
                if prev.ends_with(char::is_whitespace)
                    && split.starts_with(char::is_whitespace)
                {
                    cur += prev;
                    let end =
                        if chunk.is_detached() { usize::MAX } else { start + cur.len() };
                    latest.push(Spanned::new(
                        Chunk::Normal(std::mem::take(&mut cur)),
                        start..end,
                    ));

                    sanitize_latest(&mut latest);
                    out.push(std::mem::take(&mut latest));

                    start = end;
                    prev = split;
                    continue;
                }

                cur += prev;
                cur += keyword;
                prev = split;
            }

            cur += prev;
            let end = if chunk.is_detached() { usize::MAX } else { start + cur.len() };
            latest
                .push(Spanned::new(Chunk::Normal(std::mem::take(&mut cur)), start..end));
        } else {
            latest.push(chunk.clone());
        }
    }

    sanitize_latest(&mut latest);
    out.push(latest);
    out
}

/// Splits a chunk vector into two at the first occurrence of the character `c`.
/// `omit` controls whether the output will contain `c`.
pub(crate) fn split_at_normal_char(
    src: ChunksRef,
    c: char,
    omit: bool,
) -> (Chunks, Chunks) {
    let mut search_result = None;

    for (chunk_idx, val) in src.iter().enumerate() {
        if let Chunk::Normal(s) = &val.v {
            if let Some(str_idx) = s.find(c) {
                search_result = Some((chunk_idx, str_idx));
                break;
            }
        }
    }

    if let Some((chunk_idx, str_idx)) = search_result {
        let (v1, mut v2) = split_values(src, chunk_idx, str_idx);

        if omit {
            if let Chunk::Normal(s) = &mut v2[0].v {
                s.remove(0);
                *s = s.trim_start().to_string();
            }

            v2[0].span.start = v2[0].span.end - v2[0].v.get().len();
        }

        (v1, v2)
    } else {
        (src.to_vec(), vec![])
    }
}

/// Returns two chunk vectors with `src` split at some chunk index and
/// the string byte index `str_idx` within that chunk.
pub(crate) fn split_values(
    src: ChunksRef,
    chunk_idx: usize,
    str_idx: usize,
) -> (Chunks, Chunks) {
    let mut src = src.to_vec();
    let mut new = vec![];
    if chunk_idx >= src.len() {
        return (src, new);
    }

    if chunk_idx + 1 < src.len() {
        new.extend(src.drain(chunk_idx + 1..));
    }

    let item = src.last_mut().unwrap();
    let content = item.v.get_mut();

    let (s1, s2) = content.split_at(str_idx);

    let boundary = item.span.start.saturating_add(str_idx);
    item.span = item.span.start..boundary;
    let new_span = boundary..boundary.saturating_add(s2.len());

    let s1 = s1.trim_end().to_string();
    let s2 = s2.trim_start().to_string();

    *content = s1;

    match &item.v {
        Chunk::Normal(_) => {
            new.insert(0, Spanned::new(Chunk::Normal(s2), new_span));
        }
        Chunk::Verbatim(_) => {
            new.insert(0, Spanned::new(Chunk::Verbatim(s2), new_span));
        }
        Chunk::Math(_) => {
            new.insert(0, Spanned::new(Chunk::Math(s2), new_span));
        }
    }

    (src, new)
}

/// Returns the number of characters in the chunks.
pub(crate) fn count_num_char(chunks: ChunksRef, c: char) -> usize {
    chunks
        .iter()
        .map(|val| if let Chunk::Normal(s) = &val.v { s.matches(c).count() } else { 0 })
        .sum()
}

#[cfg(test)]
#[allow(non_snake_case)]
pub(crate) mod tests {
    use crate::Span;

    use super::*;

    pub fn N(s: &str) -> Chunk {
        Chunk::Normal(s.to_string())
    }
    pub fn V(s: &str) -> Chunk {
        Chunk::Verbatim(s.to_string())
    }

    pub fn s<T>(v: T, span: Span) -> Spanned<T> {
        Spanned::new(v, span)
    }

    pub fn d<T>(v: T) -> Spanned<T> {
        Spanned::detached(v)
    }

    #[test]
    fn test_split() {
        let vls = &[s(N("split "), 1..7), s(V("exac^tly"), 9..17), s(N("here"), 19..23)];
        let ref1 = &[s(N("split "), 1..7), s(V("exac^"), 9..14)];
        let ref2 = &[s(V("tly"), 14..17), s(N("here"), 19..23)];

        let split = split_values(vls, 1, 5);
        assert_eq!(split.0, ref1);
        assert_eq!(split.1, ref2);
    }

    #[test]
    fn test_split_at_normal_char() {
        let vls = &[
            s(N("split "), 1..7),
            s(V("not, "), 9..14),
            s(N("but rather, here"), 16..32),
        ];
        let ref1 =
            &[s(N("split "), 1..7), s(V("not, "), 9..14), s(N("but rather"), 16..26)];
        let ref2 = &[s(N("here"), 28..32)];

        let split = split_at_normal_char(vls, ',', true);
        assert_eq!(split.0, ref1);
        assert_eq!(split.1, ref2);
    }
}
