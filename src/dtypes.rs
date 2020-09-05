extern crate inflector;
extern crate numerals;
extern crate chinese_number;

use crate::parse::Chunk;
use inflector::Inflector;
use numerals::roman::Roman;
use chinese_number::{ChineseNumberToNumber, ChineseNumberCountMethod};
use regex::Regex;

lazy_static! {
    static ref RANGE_REGEX: Regex =
        Regex::new(r"(?P<s>\d+)\s*-+\s*(\d+:)?(?P<e>\d+)").unwrap();
}

#[derive(Debug)]
/// An author, editor, or some other person affiliated with the cited work.
/// When obtained through the constructor `Person::new`, the fields are trimmed.
pub struct Person {
    pub given_name: String,
    pub name: String,
    /// The prefix is placed between given name and name. It could, for example
    /// be a nobiliary particle.
    pub prefix: String,
    /// The suffix is placed after the name (e.g. "Jr.").
    pub suffix: String,
}

impl Person {
    /// Constructs a new Person from a Chunk vector according to the specs of
    /// [Nicolas Markey in "Tame the BeaST"](https://ftp.rrze.uni-erlangen.de/ctan/info/bibtex/tamethebeast/ttb_en.pdf),
    /// pp. 23-24.
    fn new(source: Vec<Chunk>) -> Self {
        let num_commas: usize = source
            .iter()
            .map(|val| {
                if let Chunk::Normal(s) = val {
                    s.matches(',').count()
                } else {
                    0
                }
            })
            .sum();

        match num_commas {
            0 => Person::from_unified(source),
            1 => {
                let (v1, v2) = split_at_normal_char(source, ',', true);

                Person::from_single_comma(v1, v2)
            }
            _ => {
                let (v1, v2) = split_at_normal_char(source, ',', true);
                let (v2, v3) = split_at_normal_char(v2, ',', true);

                Person::from_two_commas(v1, v2, v3)
            }
        }
    }

    /// Constructs new person from a Chunk Vector if in the
    /// form `<First> <Prefix> <Last>`.
    fn from_unified(source: Vec<Chunk>) -> Self {
        // Find end of first sequence of capitalized words (denominated by first
        // lowercase word), start of last capitalized seqence.
        // If there is no subsequent capitalized word, take last one.
        // Treat verbatim as capital letters

        let iter = ValueCharIter::new(&source);
        let mut word_start = true;
        let mut capital = false;
        let mut seen_lowercase = false;
        let mut seen_uppercase = false;
        let mut seen_uppercase2 = false;
        let mut cap_new_start = 0;
        let mut cap_word_end = 0;
        let mut last_word_start = 0;
        let mut last_lowercase_start = 0;
        for (index, (c, v)) in iter.clone().enumerate() {
            if c.is_whitespace() && !v {
                word_start = true;
                continue;
            }

            if word_start {
                last_word_start = index;
                capital = if v || c.is_uppercase() {
                    seen_uppercase = true;
                    if seen_lowercase && last_lowercase_start >= cap_new_start {
                        seen_uppercase2 = true;
                        cap_new_start = index;
                    }
                    true
                } else {
                    last_lowercase_start = index;
                    seen_lowercase = true;
                    false
                };
            }

            if capital && !seen_lowercase {
                cap_word_end = index;
            }

            word_start = false;
        }

        let mut name = String::new();
        let mut given_name = String::new();
        let mut prefix = String::new();

        for (index, (c, _)) in iter.clone().enumerate() {
            if (index <= cap_word_end
                && seen_lowercase
                && seen_uppercase
                && !(index == 0 && c.is_lowercase()))
                || (index < last_word_start && !seen_lowercase)
            {
                given_name.push(c);
            } else if (index < cap_new_start && cap_new_start > cap_word_end)
                || (index < last_word_start
                    && (!seen_uppercase2
                        || (last_word_start == last_lowercase_start
                            && index < cap_new_start)))
            {
                prefix.push(c);
            } else {
                name.push(c);
            }
        }

        Person {
            name: name.trim_start().to_string(),
            given_name: given_name.trim_end().to_string(),
            prefix: prefix.trim().to_string(),
            suffix: String::new(),
        }
    }

    /// Constructs new person from a Chunk Vector if in the
    /// form `<Prefix> <Last>, <First>`.
    /// `s1` corresponds to the part before the comma
    /// `s2` to the part behind it.
    ///
    /// The arguments should not contain the comma.
    fn from_single_comma(s1: Vec<Chunk>, s2: Vec<Chunk>) -> Self {
        if s2.is_empty() || (s2.len() == 1 && format_verbatim(&s2).is_empty()) {
            let formatted = format_verbatim(&s1);
            let last_space = formatted.rfind(" ").unwrap_or(0);
            let (prefix, last) = formatted.split_at(last_space);
            return Person {
                given_name: String::new(),
                name: last.trim_start().to_string(),
                prefix: prefix.trim_end().to_string(),
                suffix: String::new(),
            };
        }

        let given_name = format_verbatim(&s2);

        let mut word_start = true;
        let mut last_lower_case_end: i32 = -1;
        let mut is_lowercase = false;
        let mut last_word_start = 0;
        let mut has_seen_uppercase_words = false;
        let iter = ValueCharIter::new(&s1);
        for (index, (c, v)) in iter.clone().enumerate() {
            if c.is_whitespace() && !v {
                word_start = true;
                continue;
            }

            if word_start {
                last_word_start = index;

                if c.is_lowercase() {
                    is_lowercase = true;
                } else {
                    is_lowercase = false;
                    has_seen_uppercase_words = true;
                }
            }

            if is_lowercase {
                last_lower_case_end = index as i32;
            }

            word_start = false;
        }

        let mut name = String::new();
        let mut prefix = String::new();
        for (index, (c, _)) in iter.enumerate() {
            if (index as i32 <= last_lower_case_end && has_seen_uppercase_words)
                || (!has_seen_uppercase_words && index < last_word_start)
            {
                prefix.push(c);
            } else if has_seen_uppercase_words
                || (!has_seen_uppercase_words && index >= last_word_start)
            {
                name.push(c);
            }
        }

        Person {
            name: name.trim_start().to_string(),
            given_name: given_name.trim_start().to_string(),
            prefix: prefix.trim_end().to_string(),
            suffix: String::new(),
        }
    }

    /// Constructs new person from a Chunk Vector if in the
    /// form `<Prefix> <Last>, <Suffix>, <First>`.
    /// `s1`, `s2`, `s3` correspond to the first through third part of the
    /// value respectively.
    ///
    /// The arguments should not contain the comma.
    fn from_two_commas(s1: Vec<Chunk>, s2: Vec<Chunk>, s3: Vec<Chunk>) -> Self {
        let mut p = Person::from_single_comma(s1, s3);
        p.suffix = format_verbatim(&s2);
        p
    }
}

/// Parse range fields with a number of ranges and an amount of dashes seperating
/// start from end.
fn parse_ranges(source: Vec<Chunk>) -> Vec<std::ops::Range<u32>> {
    let range_vecs = split_token_lists(source, ",");
    let mut res = vec![];
    for range_candidate in range_vecs.iter().map(|f| format_verbatim(f)) {
        let caps = RANGE_REGEX.captures(&range_candidate);
        if let Some(caps) = caps {
            let start: u32 =
                str::parse(caps.name("s").expect("start is mandatory").as_str())
                    .expect("Only queried for digits");
            let end: u32 =
                str::parse(caps.name("e").expect("start is mandatory").as_str())
                    .expect("Only queried for digits");

            res.push(start .. end);
        }
    }

    res
}

/// Parse integers. This method will accept arabic, roman, and chinese numerals.
fn parse_integers(source: &[Chunk]) -> Result<i64, ()> {
    let s = format_verbatim(source);
    let s_t = s.trim();

    if let Ok(n) = str::parse::<i64>(s_t) {
        Ok(n)
    } else if let Some(roman) = Roman::parse(s_t) {
        Ok(Roman::from(roman).value() as i64)
    } else if let Ok(n) = s_t.parse_chinese_number(ChineseNumberCountMethod::TenThousand) {
        Ok(n)
    } else {
        Err(())
    }
}

#[derive(Clone)]
/// This struct is an Iterator for Chunk slices that will iterate through the
/// contained characters indicating whether they are Verbatim or not.
/// Chunk types other than `Normal` or `Verbatim` will be ommitted.
struct ValueCharIter<'s> {
    vals: &'s [Chunk],
    vec_index: usize,
    val_index: usize,
}

impl<'s> ValueCharIter<'s> {
    fn new(vals: &'s [Chunk]) -> Self {
        ValueCharIter { vals, vec_index: 0, val_index: 0 }
    }
}

impl<'s> Iterator for ValueCharIter<'s> {
    type Item = (char, bool);

    fn next(&mut self) -> Option<Self::Item> {
        if self.vec_index >= self.vals.len() {
            return None;
        }

        let mut s;
        let mut verb;
        while {
            let temp = if let Chunk::Normal(s) = &self.vals[self.vec_index] {
                (s.chars().nth(self.val_index), false)
            } else if let Chunk::Verbatim(s) = &self.vals[self.vec_index] {
                (s.chars().nth(self.val_index), true)
            } else {
                (None, false)
            };
            s = temp.0;
            verb = temp.1;
            s.is_none()
        } {
            self.val_index = 0;
            self.vec_index += 1;
            if self.vec_index >= self.vals.len() {
                return None;
            }

            if matches!(&self.vals[self.vec_index], Chunk::Normal(_) | Chunk::Verbatim(_))
            {
                continue;
            }
        }

        self.val_index += 1;

        Some((s.expect("Has to be some"), verb))
    }
}

/// Returns two Chunk Vectors with `src` split at Chunk index `vi` and
/// char index `si` within that chunk.
fn split_values(mut src: Vec<Chunk>, vi: usize, si: usize) -> (Vec<Chunk>, Vec<Chunk>) {
    if vi >= src.len() {
        return (vec![], src);
    }

    let mut new = vec![];
    while src.len() > vi + 1 {
        new.insert(0, src.pop().expect("Index checked above"));
    }

    let item = src.pop().expect("Index checked above");
    let (content, verb) = match item {
        Chunk::Normal(s) => (s, false),
        Chunk::Verbatim(s) => (s, true),
        Chunk::Resolve(s) => (s, true),
        Chunk::CommandName(s, verb) => (s, verb),
        Chunk::CommandArgs(s) => (s, true),
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

/// Splits a Chunk vector into two at the first occurrance of the character `c`.
/// `omit` controls whether the output will contain `c`.
fn split_at_normal_char(
    src: Vec<Chunk>,
    c: char,
    omit: bool,
) -> (Vec<Chunk>, Vec<Chunk>) {
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

/// Formats a Chunk slice in sentence case.
pub fn format_sentence(vals: &[Chunk]) -> String {
    let mut out = String::new();
    let mut first = true;
    for val in vals {
        if let Chunk::Normal(s) = val {
            if first && !s.is_empty() {
                first = false;
                out += &s.to_title_case();
            } else {
                out += &s.to_lowercase();
            }
        } else if let Chunk::Verbatim(s) = val {
            out += s;
        }
    }

    out
}

/// Outputs a Chunk slice in verbatim.
pub fn format_verbatim(vals: &[Chunk]) -> String {
    let mut out = String::new();
    for val in vals {
        if let Chunk::Normal(s) = val {
            out += s;
        } else if let Chunk::Verbatim(s) = val {
            out += s;
        }
    }

    out
}

/// Splits Chunk Vectors that are a token list as defined per the
/// [BibLaTeX Manual](http://ctan.ebinger.cc/tex-archive/macros/latex/contrib/biblatex/doc/biblatex.pdf)
/// p. 16 along occurances of the keyword.
pub fn split_token_lists(vals: Vec<Chunk>, keyword: &str) -> Vec<Vec<Chunk>> {
    let mut out = vec![];
    let mut latest: Vec<Chunk> = vec![];
    for val in vals {
        if let Chunk::Normal(s) = val {
            let mut target = s.as_str();

            while let Some(pos) = target.find(keyword) {
                let first = target[.. pos].trim_end();
                latest.push(Chunk::Normal(first.to_string()));
                out.push(latest);
                latest = vec![];
                target = target[pos + keyword.len() ..].trim_start();
            }

            latest.push(Chunk::Normal(target.to_string()));
        } else {
            latest.push(val);
        }
    }

    out.push(latest);

    out
}

#[cfg(test)]
mod tests {
    use super::{split_at_normal_char, split_values, Person, ValueCharIter, parse_ranges};
    use crate::parse::Chunk;

    #[allow(non_snake_case)]
    fn R(s: &str) -> Chunk {
        Chunk::Resolve(s.to_string())
    }

    #[allow(non_snake_case)]
    fn N(s: &str) -> Chunk {
        Chunk::Normal(s.to_string())
    }

    #[allow(non_snake_case)]
    fn V(s: &str) -> Chunk {
        Chunk::Verbatim(s.to_string())
    }

    #[test]
    fn test_value_iterator() {
        let vls = vec![N("it "), R("crap"), V("te")];
        let mut iter = ValueCharIter::new(&vls);
        assert_eq!(iter.next(), Some(('i', false)));
        assert_eq!(iter.next(), Some(('t', false)));
        assert_eq!(iter.next(), Some((' ', false)));
        assert_eq!(iter.next(), Some(('t', true)));
        assert_eq!(iter.next(), Some(('e', true)));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_value_split() {
        let vls = vec![N("split "), V("exac^tly"), N("here")];
        let ref1 = vec![N("split "), V("exac^")];
        let ref2 = vec![V("tly"), N("here")];
        let split = split_values(vls, 1, 5);
        assert_eq!(split.0, ref1);
        assert_eq!(split.1, ref2);
    }

    #[test]
    fn test_person_comma() {
        let p = Person::new(vec![N("jean de la fontaine,")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "jean de la");
        assert_eq!(p.given_name, "");

        let p = Person::new(vec![N("de la fontaine, Jean")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "de la");
        assert_eq!(p.given_name, "Jean");

        let p = Person::new(vec![N("De La Fontaine, Jean")]);
        assert_eq!(p.name, "De La Fontaine");
        assert_eq!(p.prefix, "");
        assert_eq!(p.given_name, "Jean");

        let p = Person::new(vec![N("De la Fontaine, Jean")]);
        assert_eq!(p.name, "Fontaine");
        assert_eq!(p.prefix, "De la");
        assert_eq!(p.given_name, "Jean");

        let p = Person::new(vec![N("de La Fontaine, Jean")]);
        assert_eq!(p.name, "La Fontaine");
        assert_eq!(p.prefix, "de");
        assert_eq!(p.given_name, "Jean");
    }

    #[test]
    fn test_person_no_comma() {
        let p = Person::new(vec![N("jean de la fontaine")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "jean de la");
        assert_eq!(p.given_name, "");

        let p = Person::new(vec![N("Jean de la fontaine")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "de la");
        assert_eq!(p.given_name, "Jean");

        let p = Person::new(vec![N("Jean "), V("de"), N(" la fontaine")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "la");
        assert_eq!(p.given_name, "Jean de");

        let p = Person::new(vec![N("Jean "), V("de"), N(" "), V("la"), N(" fontaine")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "");
        assert_eq!(p.given_name, "Jean de la");

        let p = Person::new(vec![N("jean "), V("de"), N(" "), V("la"), N(" fontaine")]);
        assert_eq!(p.name, "de la fontaine");
        assert_eq!(p.prefix, "jean");
        assert_eq!(p.given_name, "");

        let p = Person::new(vec![N("Jean De La Fontaine")]);
        assert_eq!(p.name, "Fontaine");
        assert_eq!(p.prefix, "");
        assert_eq!(p.given_name, "Jean De La");

        let p = Person::new(vec![N("jean De la Fontaine")]);
        assert_eq!(p.name, "Fontaine");
        assert_eq!(p.prefix, "jean De la");
        assert_eq!(p.given_name, "");

        let p = Person::new(vec![N("Jean de La Fontaine")]);
        assert_eq!(p.name, "La Fontaine");
        assert_eq!(p.prefix, "de");
        assert_eq!(p.given_name, "Jean");

        let p = Person::new(vec![N("")]);
        assert_eq!(p.name, "");
        assert_eq!(p.prefix, "");
        assert_eq!(p.given_name, "");
    }

    #[test]
    fn test_person_two_comma() {
        let p = Person::new(vec![N("Mudd, Sr., Harcourt Fenton")]);
        assert_eq!(p.name, "Mudd");
        assert_eq!(p.prefix, "");
        assert_eq!(p.suffix, "Sr.");
        assert_eq!(p.given_name, "Harcourt Fenton");
    }

    #[test]
    fn test_value_split_at_normal_char() {
        let vls = vec![N("split "), V("not, "), N("but rather, here")];
        let ref1 = vec![N("split "), V("not, "), N("but rather")];
        let ref2 = vec![N("here")];
        let split = split_at_normal_char(vls, ',', true);
        assert_eq!(split.0, ref1);
        assert_eq!(split.1, ref2);
    }

    #[test]
    fn test_ranges() {
        let ranges = vec![N("31--43,21:4-21:6,  194 --- 245")];
        let res = parse_ranges(ranges);
        assert_eq!(res[0], 31 .. 43);
        assert_eq!(res[1], 4 .. 6);
        assert_eq!(res[2], 194 .. 245);
    }
}
