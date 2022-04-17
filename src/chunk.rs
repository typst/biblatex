use crate::resolve::is_escapable;
use crate::types::Type;
use crate::{Span, Spanned, TypeError};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A sequence of chunks.
pub type Chunks = Vec<Spanned<Chunk>>;

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
    pub fn get_escaped(&self, verbatim_mode: bool) -> String {
        let mut s = String::new();
        for c in self.get().chars() {
            if is_escapable(c, verbatim_mode) {
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
    fn to_biblatex_string(&self, verbatim_mode: bool) -> String;
}

impl ChunksExt for [Spanned<Chunk>] {
    fn parse<T: Type>(&self) -> Result<T, TypeError> {
        T::from_chunks(self)
    }

    fn format_sentence(&self) -> String {
        let mut out = String::new();
        let mut first = true;

        for val in self {
            match &val.v {
                Chunk::Normal(s) => {
                    for c in s.chars() {
                        if first {
                            out.extend(c.to_uppercase());
                        } else {
                            out.extend(c.to_lowercase());
                        }
                        first = false;
                    }
                }
                Chunk::Verbatim(s) => {
                    out.push_str(&s);
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
        for val in self {
            match &val.v {
                Chunk::Normal(s) => out += s,
                Chunk::Verbatim(s) => out += s,
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
        start .. end
    }

    fn to_biblatex_string(&self, verbatim_mode: bool) -> String {
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

            res.push_str(&chunk.v.get_escaped(verbatim_mode));

            if let Chunk::Math(_) = &chunk.v {
                res.push('$');
            }
        }

        for _ in 0 .. if extra_brace { 2 } else { 1 } {
            res.push('}');
        }

        res
    }
}

/// An iterator over the characters in each chunk, indicating whether they are
/// verbatim or not. Chunk types other than `Normal` or `Verbatim` are ommitted.
pub(crate) fn chunk_chars(
    chunks: &[Spanned<Chunk>],
) -> impl Iterator<Item = (char, bool)> + '_ {
    chunks.iter().flat_map(|chunk| {
        let (s, verbatim) = chunk.v.get_and_verb();

        s.chars().map(move |c| (c, verbatim))
    })
}

/// Combines the cunks, interlacing with the separator.
pub(crate) fn join_chunk_list(chunks: &[Spanned<Chunk>], sep: &str) -> Chunks {
    let mut res = vec![];
    let mut first = true;

    for chunk in chunks {
        if first {
            first = false;
        } else {
            res.push(Spanned::new(
                Chunk::Normal(sep.to_string()),
                chunk.span.start .. chunk.span.start,
            ));
        }

        res.push(chunk.clone());
    }

    res
}

/// Splits chunk vectors that are a token lists as defined per the
/// [BibLaTeX Manual][manual] p. 16 along occurances of the keyword.
///
/// [manual]: http://ctan.ebinger.cc/tex-archive/macros/latex/contrib/biblatex/doc/biblatex.pdf
pub(crate) fn split_token_lists(vals: &[Spanned<Chunk>], keyword: &str) -> Vec<Chunks> {
    let mut out = vec![];
    let mut latest = vec![];

    for val in vals {
        if let Chunk::Normal(s) = &val.v {
            let mut target = s.as_str();
            let mut start = val.span.start;

            while let Some(pos) = target.find(keyword) {
                let first = target[.. pos].trim_end();
                latest.push(Spanned::new(
                    Chunk::Normal(first.to_string()),
                    start .. start + pos,
                ));
                out.push(std::mem::take(&mut latest));

                target = target[pos + keyword.len() ..].trim_start();
                start += pos + keyword.len();
            }

            latest.push(Spanned::new(
                Chunk::Normal(target.to_string()),
                start .. val.span.end,
            ));
        } else {
            latest.push(val.clone());
        }
    }

    out.push(latest);
    out
}

/// Splits a chunk vector into two at the first occurrance of the character `c`.
/// `omit` controls whether the output will contain `c`.
pub(crate) fn split_at_normal_char(
    src: &[Spanned<Chunk>],
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
    src: &[Spanned<Chunk>],
    chunk_idx: usize,
    str_idx: usize,
) -> (Chunks, Chunks) {
    let mut src = src.to_vec();
    let mut new = vec![];
    if chunk_idx >= src.len() {
        return (src, new);
    }

    if chunk_idx + 1 < src.len() {
        new.extend(src.drain(chunk_idx + 1 ..));
    }

    let item = src.last_mut().unwrap();
    let content = item.v.get_mut();

    let (s1, s2) = content.split_at(str_idx);

    let boundry = item.span.start + str_idx;
    item.span = item.span.start .. boundry;
    let new_span = boundry .. boundry + s2.len();

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

    #[test]
    fn test_split() {
        let vls = &[
            s(N("split "), 1 .. 7),
            s(V("exac^tly"), 9 .. 17),
            s(N("here"), 19 .. 23),
        ];
        let ref1 = &[s(N("split "), 1 .. 7), s(V("exac^"), 9 .. 14)];
        let ref2 = &[s(V("tly"), 14 .. 17), s(N("here"), 19 .. 23)];

        let split = split_values(vls, 1, 5);
        assert_eq!(split.0, ref1);
        assert_eq!(split.1, ref2);
    }

    #[test]
    fn test_split_at_normal_char() {
        let vls = &[
            s(N("split "), 1 .. 7),
            s(V("not, "), 9 .. 14),
            s(N("but rather, here"), 16 .. 32),
        ];
        let ref1 = &[
            s(N("split "), 1 .. 7),
            s(V("not, "), 9 .. 14),
            s(N("but rather"), 16 .. 26),
        ];
        let ref2 = &[s(N("here"), 28 .. 32)];

        let split = split_at_normal_char(vls, ',', true);
        assert_eq!(split.0, ref1);
        assert_eq!(split.1, ref2);
    }
}
