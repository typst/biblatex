use std::fmt::{self, Display, Formatter};

use crate::chunk::*;
use crate::Type;

/// An author, editor, or some other person affiliated with a cited work.
///
/// When parsed through [`Person::parse`], the whitespace is trimmed from the
/// fields.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct Person {
    /// The surname / family name / last name.
    pub name: String,
    /// The given name / first name / forename.
    pub given_name: String,
    /// The prefix is placed between given name and name. It could, for example,
    /// be a nobiliary particle.
    pub prefix: String,
    /// The suffix is placed after the name (e.g. "Jr.").
    pub suffix: String,
}

impl Person {
    /// Constructs a new person from a chunk vector according to the specs of
    /// [Nicolas Markey in "Tame the BeaST"][taming], pp. 23-24.
    ///
    /// [taming]: https://ftp.rrze.uni-erlangen.de/ctan/info/bibtex/tamethebeast/ttb_en.pdf
    pub fn parse(chunks: &[Chunk]) -> Self {
        let num_commas: usize = chunks
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
            0 => Self::parse_unified(&chunks),
            1 => {
                let (v1, v2) = split_at_normal_char(chunks, ',', true);
                Self::parse_single_comma(&v1, &v2)
            }
            _ => {
                let (v1, v2) = split_at_normal_char(chunks, ',', true);
                let (v2, v3) = split_at_normal_char(&v2, ',', true);
                Self::parse_two_commas(&v1, &v2, &v3)
            }
        }
    }

    /// Constructs new person from a chunk slice if in the
    /// form `<First> <Prefix> <Last>`.
    fn parse_unified(chunks: &[Chunk]) -> Self {
        // Find end of first sequence of capitalized words (denominated by first
        // lowercase word), start of last capitalized seqence.
        // If there is no subsequent capitalized word, take last one.
        // Treat verbatim as capital letters
        let mut word_start = true;
        let mut capital = false;
        let mut seen_lowercase = false;
        let mut seen_uppercase = false;
        let mut seen_uppercase2 = false;
        let mut cap_new_start = 0;
        let mut cap_word_end = 0;
        let mut last_word_start = 0;
        let mut last_lowercase_start = 0;

        for (index, (c, v)) in chunk_chars(&chunks).enumerate() {
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

        for (index, (c, _)) in chunk_chars(&chunks).enumerate() {
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

        Self {
            name: name.trim_start().to_string(),
            given_name: given_name.trim_end().to_string(),
            prefix: prefix.trim().to_string(),
            suffix: String::new(),
        }
    }

    /// Constructs new person from chunk slices if in the
    /// form `<Prefix> <Last>, <First>`.
    /// - `s1` corresponds to the part before the comma,
    /// - `s2` to the part behind it.
    ///
    /// The arguments should not contain the comma.
    fn parse_single_comma(s1: &[Chunk], s2: &[Chunk]) -> Self {
        if s2.is_empty() || (s2.len() == 1 && s2.format_verbatim().is_empty()) {
            let formatted = s1.format_verbatim();
            let last_space = formatted.rfind(' ').unwrap_or(0);
            let (prefix, last) = formatted.split_at(last_space);
            return Self {
                given_name: String::new(),
                name: last.trim_start().to_string(),
                prefix: prefix.trim_end().to_string(),
                suffix: String::new(),
            };
        }

        let given_name = s2.format_verbatim();

        let mut word_start = true;
        let mut last_lower_case_end: i32 = -1;
        let mut is_lowercase = false;
        let mut last_word_start = 0;
        let mut has_seen_uppercase_words = false;

        for (index, (c, v)) in chunk_chars(&s1).enumerate() {
            if c.is_whitespace() && !v {
                word_start = true;
                continue;
            }

            if word_start {
                last_word_start = index;

                if c.is_lowercase() || v {
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
        for (index, (c, _)) in chunk_chars(&s1).enumerate() {
            if (index as i32 <= last_lower_case_end && has_seen_uppercase_words)
                || (!has_seen_uppercase_words && index < last_word_start)
            {
                prefix.push(c);
            } else if has_seen_uppercase_words || index >= last_word_start {
                name.push(c);
            }
        }

        Self {
            name: name.trim_start().to_string(),
            given_name: given_name.trim_start().to_string(),
            prefix: prefix.trim_end().to_string(),
            suffix: String::new(),
        }
    }

    /// Constructs new person from chunk slices if in the
    /// form `<Prefix> <Last>, <Suffix>, <First>`.
    ///
    /// `s1`, `s2`, `s3` correspond to the first through third part of the
    /// value respectively.
    ///
    /// The arguments should not contain the comma.
    fn parse_two_commas(s1: &[Chunk], s2: &[Chunk], s3: &[Chunk]) -> Self {
        let mut p = Self::parse_single_comma(s1, s3);
        p.suffix = s2.format_verbatim();
        p
    }
}

impl Type for Vec<Person> {
    fn from_chunks(chunks: &[Chunk]) -> Option<Self> {
        Some(
            split_token_lists(chunks, " and ")
                .into_iter()
                .map(|subchunks| Person::parse(&subchunks))
                .collect(),
        )
    }

    fn to_chunks(&self) -> Chunks {
        self.iter()
            .map(|p| {
                let prefix = if let Some(c) = p.prefix.chars().next() {
                    if c.is_uppercase() {
                        (Some(Chunk::Verbatim(p.prefix.clone())), " ".to_string())
                    } else {
                        (None, format!("{} ", p.prefix))
                    }
                } else {
                    (None, String::new())
                };

                let name_str = if !p.suffix.is_empty() {
                    format!("{}{}, {}, {}", prefix.1, p.name, p.suffix, p.given_name)
                } else {
                    format!("{}{}, {}", prefix.1, p.name, p.given_name)
                };
                let mut res = vec![Chunk::Normal(name_str)];
                if let Some(pre_chunk) = prefix.0 {
                    res.insert(0, pre_chunk);
                }

                res
            })
            .collect::<Vec<Chunks>>()
            .to_chunks()
    }
}

impl Display for Person {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if !self.given_name.is_empty() {
            write!(f, "{} ", self.given_name)?;
        }

        if !self.prefix.is_empty() {
            write!(f, "{} ", self.prefix)?;
        }

        write!(f, "{}", self.name)?;

        if !self.suffix.is_empty() {
            write!(f, " {}", self.suffix)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use crate::{chunk::tests::*, resolve::resolve};

    #[test]
    fn test_person_comma() {
        let p = Person::parse(&[N("jean de la fontaine,")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "jean de la");
        assert_eq!(p.given_name, "");
        assert_eq!(vec![p].to_chunks(), vec![N("jean de la fontaine, ")]);

        let p = Person::parse(&[N("de la fontaine, Jean")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "de la");
        assert_eq!(p.given_name, "Jean");
        assert_eq!(vec![p].to_chunks(), vec![N("de la fontaine, Jean")]);

        let p = Person::parse(&[N("De La Fontaine, Jean")]);
        assert_eq!(p.name, "De La Fontaine");
        assert_eq!(p.prefix, "");
        assert_eq!(p.given_name, "Jean");
        assert_eq!(vec![p].to_chunks(), vec![N("De La Fontaine, Jean")]);

        let p = Person::parse(&[V("De La"), N(" Fontaine, Jean")]);
        assert_eq!(p.name, "Fontaine");
        assert_eq!(p.prefix, "De La");
        assert_eq!(p.given_name, "Jean");
        assert_eq!(vec![p].to_chunks(), vec![V("De La"), N(" Fontaine, Jean")]);

        let p = Person::parse(&[N("De la Fontaine, Jean")]);
        assert_eq!(p.name, "Fontaine");
        assert_eq!(p.prefix, "De la");
        assert_eq!(p.given_name, "Jean");

        let p = Person::parse(&[N("de La Fontaine, Jean")]);
        assert_eq!(p.name, "La Fontaine");
        assert_eq!(p.prefix, "de");
        assert_eq!(p.given_name, "Jean");
    }

    #[test]
    fn test_person_no_comma() {
        let p = Person::parse(&[N("")]);
        assert_eq!(p.name, "");
        assert_eq!(p.prefix, "");
        assert_eq!(p.given_name, "");

        let p = Person::parse(&[N("jean de la fontaine")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "jean de la");
        assert_eq!(p.given_name, "");

        let p = Person::parse(&[N("Jean de la fontaine")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "de la");
        assert_eq!(p.given_name, "Jean");

        let p = Person::parse(&[N("Jean "), V("de"), N(" la fontaine")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "la");
        assert_eq!(p.given_name, "Jean de");

        let p = Person::parse(&[N("Jean "), V("de"), N(" "), V("la"), N(" fontaine")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "");
        assert_eq!(p.given_name, "Jean de la");

        let p = Person::parse(&[N("jean "), V("de"), N(" "), V("la"), N(" fontaine")]);
        assert_eq!(p.name, "de la fontaine");
        assert_eq!(p.prefix, "jean");
        assert_eq!(p.given_name, "");

        let p = Person::parse(&[N("Jean De La Fontaine")]);
        assert_eq!(p.name, "Fontaine");
        assert_eq!(p.prefix, "");
        assert_eq!(p.given_name, "Jean De La");

        let p = Person::parse(&[N("jean De la Fontaine")]);
        assert_eq!(p.name, "Fontaine");
        assert_eq!(p.prefix, "jean De la");
        assert_eq!(p.given_name, "");

        let p = Person::parse(&[N("Jean de La Fontaine")]);
        assert_eq!(p.name, "La Fontaine");
        assert_eq!(p.prefix, "de");
        assert_eq!(p.given_name, "Jean");
    }

    #[test]
    fn test_person_two_comma() {
        let p = Person::parse(&[N("Mudd, Sr., Harcourt Fenton")]);
        assert_eq!(p.name, "Mudd");
        assert_eq!(p.prefix, "");
        assert_eq!(p.suffix, "Sr.");
        assert_eq!(p.given_name, "Harcourt Fenton");
    }

    #[test]
    fn person_with_command() {
        let value ="{Syperek, Marcin and Dusanowski, {\\L}ukasz and Misiewicz, Jan and Langer, Fabian and Forchel, Alfred}";
        let res = resolve(value, &HashMap::new()).unwrap();
        let pers: Vec<Person> = Vec::<Person>::from_chunks(&res).unwrap();
        assert_eq!(pers.len(), 5);
        assert_eq!(pers[1].given_name, "Łukasz");
        assert_eq!(pers[2].given_name, "Jan");
    }
}
