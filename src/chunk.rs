use crate::resolve::is_escapable;
use crate::types::Type;
use serde::{Deserialize, Serialize};

/// A sequence of chunks.
pub type Chunks = Vec<Chunk>;

/// Represents one part of a field value.
#[derive(Debug, Clone, Eq, PartialEq, Deserialize, Serialize)]
pub enum Chunk {
    /// Normal values within quotes or single braces subject to
    /// capitalization formatting.
    Normal(String),
    /// Values nested in braces that are to be printed like specified
    /// in the file. Escapes keywords.
    ///
    /// Example: `"Inside {NASA}"` or `{Memes are {gReAT}}`.
    Verbatim(String),
}

/// Additional methods for chunk slices.
pub trait ChunksExt {
    /// Parse the chunks into a type.
    fn parse<T: Type>(&self) -> Option<T>;

    /// Format the chunks in sentence case.
    fn format_sentence(&self) -> String;

    /// Format the chunks verbatim.
    fn format_verbatim(&self) -> String;

    /// Serialize the chunks into a BibLaTeX string.
    fn to_biblatex_string(&self) -> String;
}

impl ChunksExt for [Chunk] {
    fn parse<T: Type>(&self) -> Option<T> {
        T::from_chunks(self)
    }

    fn format_sentence(&self) -> String {
        let mut out = String::new();
        let mut first = true;
        for val in self {
            if let Chunk::Normal(s) = val {
                for c in s.chars() {
                    if first {
                        out.extend(c.to_uppercase());
                    } else {
                        out.extend(c.to_lowercase());
                    }
                    first = false;
                }
            } else if let Chunk::Verbatim(s) = val {
                out += s;
            }
            first = false;
        }

        out
    }

    fn format_verbatim(&self) -> String {
        let mut out = String::new();
        for val in self {
            if let Chunk::Normal(s) = val {
                out += s;
            } else if let Chunk::Verbatim(s) = val {
                out += s;
            }
        }

        out
    }

    fn to_biblatex_string(&self) -> String {
        let iter = chunk_chars(self);
        let mut res = String::new();
        res.push('{');
        let mut braces = 1;

        for (c, v) in iter {
            if v && braces <= 1 {
                res.push('{');
                braces += 1;
            } else if !v && braces > 1 {
                res.push('}');
                braces -= 1;
            }

            if is_escapable(c) || c == '\\' {
                res.push('\\');
            }

            res.push(c);
        }

        for _ in 0..braces {
            res.push('}');
        }

        res
    }
}

/// An iterator over the characters in each chunk, indicating whether they are
/// verbatim or not. Chunk types other than `Normal` or `Verbatim` are ommitted.
pub(crate) fn chunk_chars(chunks: &[Chunk]) -> impl Iterator<Item = (char, bool)> + '_ {
    chunks.iter().flat_map(|chunk| {
        let (s, verbatim) = match chunk {
            Chunk::Normal(s) => (s, false),
            Chunk::Verbatim(s) => (s, true),
        };

        s.chars().map(move |c| (c, verbatim))
    })
}

/// Combines the cunks, interlacing with the separator.
pub(crate) fn join_chunk_list(chunks: &[Chunk], sep: &str) -> Chunks {
    let mut res = vec![];
    let mut chunks = chunks.to_vec().into_iter();
    if let Some(chunk) = chunks.next() {
        res.push(chunk);

        for chunk in chunks {
            res.push(Chunk::Normal(sep.to_string()));
            res.push(chunk);
        }
    }
    res
}

/// Splits chunk vectors that are a token lists as defined per the
/// [BibLaTeX Manual][manual] p. 16 along occurances of the keyword.
///
/// [manual]: http://ctan.ebinger.cc/tex-archive/macros/latex/contrib/biblatex/doc/biblatex.pdf
pub(crate) fn split_token_lists(vals: &[Chunk], keyword: &str) -> Vec<Chunks> {
    let mut out = vec![];
    let mut latest = vec![];

    for val in vals {
        if let Chunk::Normal(s) = val {
            let mut target = s.as_str();

            while let Some(pos) = target.find(keyword) {
                let first = target[..pos].trim_end();
                latest.push(Chunk::Normal(first.to_string()));
                out.push(latest);
                latest = vec![];
                target = target[pos + keyword.len()..].trim_start();
            }

            latest.push(Chunk::Normal(target.to_string()));
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
    src: &[Chunk],
    c: char,
    omit: bool,
) -> (Chunks, Chunks) {
    let mut found = false;
    let mut len = src.len();
    let mut si = 0;
    for (index, val) in src.iter().enumerate() {
        if let Chunk::Normal(s) = val {
            if let Some(pos) = s.find(c) {
                found = true;
                si = pos;
                len = index;
            }
        } else {
            continue;
        }
    }

    let (v1, mut v2) = split_values(src, len, si);

    if omit && found {
        let first = v2[0].clone();
        if let Chunk::Normal(mut s) = first {
            s.remove(0);
            s = s.trim_start().to_string();
            v2[0] = Chunk::Normal(s);
        }
    }

    (v1, v2)
}

/// Returns two chunk vectors with `src` split at chunk index `vi` and
/// char index `si` within that chunk.
pub(crate) fn split_values(src: &[Chunk], vi: usize, si: usize) -> (Chunks, Chunks) {
    let mut src = src.to_vec();
    if vi >= src.len() {
        return (vec![], src);
    }

    let mut new = vec![];
    while src.len() > vi + 1 {
        new.insert(0, src.pop().expect("index checked above"));
    }

    let item = src.pop().expect("index checked above");
    let (content, verb) = match item {
        Chunk::Normal(s) => (s, false),
        Chunk::Verbatim(s) => (s, true),
    };

    let (s1, s2) = content.split_at(si);
    if verb {
        src.push(Chunk::Verbatim(s1.trim_end().to_string()));
        new.insert(0, Chunk::Verbatim(s2.trim_start().to_string()));
    } else {
        src.push(Chunk::Normal(s1.trim_end().to_string()));
        new.insert(0, Chunk::Normal(s2.trim_start().to_string()));
    }

    (src, new)
}

#[cfg(test)]
#[allow(non_snake_case)]
pub(crate) mod tests {
    use super::*;

    pub fn N(s: &str) -> Chunk {
        Chunk::Normal(s.to_string())
    }
    pub fn V(s: &str) -> Chunk {
        Chunk::Verbatim(s.to_string())
    }

    #[test]
    fn test_chars_iterator() {
        let vls = &[N("it "), V("te")];
        let mut iter = chunk_chars(vls);
        assert_eq!(iter.next(), Some(('i', false)));
        assert_eq!(iter.next(), Some(('t', false)));
        assert_eq!(iter.next(), Some((' ', false)));
        assert_eq!(iter.next(), Some(('t', true)));
        assert_eq!(iter.next(), Some(('e', true)));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_split() {
        let vls = &[N("split "), V("exac^tly"), N("here")];
        let ref1 = &[N("split "), V("exac^")];
        let ref2 = &[V("tly"), N("here")];
        let split = split_values(vls, 1, 5);
        assert_eq!(split.0, ref1);
        assert_eq!(split.1, ref2);
    }

    #[test]
    fn test_split_at_normal_char() {
        let vls = &[N("split "), V("not, "), N("but rather, here")];
        let ref1 = &[N("split "), V("not, "), N("but rather")];
        let ref2 = &[N("here")];
        let split = split_at_normal_char(vls, ',', true);
        assert_eq!(split.0, ref1);
        assert_eq!(split.1, ref2);
    }
}
