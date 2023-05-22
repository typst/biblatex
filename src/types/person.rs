use std::fmt::{self, Display, Formatter};

use crate::{chunk::*, Spanned};
use crate::{Type, TypeError};

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
    pub fn parse(chunks: ChunksRef) -> Self {
        let num_commas: usize =
            chunks
                .iter()
                .map(|val| {
                    if let Chunk::Normal(s) = &val.v {
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
    fn parse_unified(chunks: ChunksRef) -> Self {
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
    fn parse_single_comma(s1: ChunksRef, s2: ChunksRef) -> Self {
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
    fn parse_two_commas(s1: ChunksRef, s2: ChunksRef, s3: ChunksRef) -> Self {
        let mut p = Self::parse_single_comma(s1, s3);
        p.suffix = s2.format_verbatim();
        p
    }
}

impl Type for Vec<Person> {
    fn from_chunks(chunks: ChunksRef) -> Result<Self, TypeError> {
        Ok(split_token_lists_surrounded_by_whitespace(chunks, "and")
            .into_iter()
            .map(|subchunks| Person::parse(&subchunks))
            .collect())
    }

    fn to_chunks(&self) -> Chunks {
        self.iter()
            .map(|p| {
                let prefix = if let Some(c) = p.prefix.chars().next() {
                    if c.is_uppercase() {
                        (
                            Some(Spanned::detached(Chunk::Verbatim(p.prefix.clone()))),
                            " ".to_string(),
                        )
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

                let mut res = vec![Spanned::detached(Chunk::Normal(name_str))];
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
    use crate::chunk::tests::*;

    #[test]
    fn test_list_of_names() {
        let names =
            String::from("Johannes Gutenberg and Aldus Manutius and Claude Garamond");
        let range = std::ops::Range { start: 0, end: names.len() };
        let people = &[Spanned::new(Chunk::Normal(names), range)];
        let people: Vec<Person> = Type::from_chunks(people).unwrap();
        assert_eq!(people.len(), 3);

        assert_eq!(people[0].name, "Gutenberg");
        assert_eq!(people[0].prefix, "");
        assert_eq!(people[0].given_name, "Johannes");

        assert_eq!(people[1].name, "Manutius");
        assert_eq!(people[1].prefix, "");
        assert_eq!(people[1].given_name, "Aldus");

        assert_eq!(people[2].name, "Garamond");
        assert_eq!(people[2].prefix, "");
        assert_eq!(people[2].given_name, "Claude");
    }

    #[test]
    fn test_list_of_names_multilines() {
        let names = String::from(
            "Johannes Gutenberg and
Aldus Manutius and
Claude Garamond",
        );
        let range = std::ops::Range { start: 0, end: names.len() };
        let people = &[Spanned::new(Chunk::Normal(names), range)];
        let people1: Vec<Person> = Type::from_chunks(people).unwrap();
        assert_eq!(people1.len(), 3);

        let names = String::from(
            "Johannes Gutenberg
and
Aldus Manutius
and
Claude Garamond",
        );
        let range = std::ops::Range { start: 0, end: names.len() };
        let people = &[Spanned::new(Chunk::Normal(names), range)];
        let people2: Vec<Person> = Type::from_chunks(people).unwrap();
        assert_eq!(people2.len(), 3);

        let names = String::from(
            "Johannes Gutenberg
and
Aldus Manutius and
Claude Garamond",
        );
        let range = std::ops::Range { start: 0, end: names.len() };
        let people = &[Spanned::new(Chunk::Normal(names), range)];
        let people3: Vec<Person> = Type::from_chunks(people).unwrap();
        assert_eq!(people3.len(), 3);

        assert_eq!(people1, people2);
        assert_eq!(people2, people3);

        assert_eq!(people1[0].name, "Gutenberg");
        assert_eq!(people1[0].prefix, "");
        assert_eq!(people1[0].given_name, "Johannes");

        assert_eq!(people1[1].name, "Manutius");
        assert_eq!(people1[1].prefix, "");
        assert_eq!(people1[1].given_name, "Aldus");

        assert_eq!(people1[2].name, "Garamond");
        assert_eq!(people1[2].prefix, "");
        assert_eq!(people1[2].given_name, "Claude");
    }

    #[test]
    fn test_leading_and() {
        let names = String::from(
            "and Gutenberg, Johannes and
Aldus Manutius and
Claude Garamond",
        );
        let range = std::ops::Range { start: 0, end: names.len() };
        let people = &[Spanned::new(Chunk::Normal(names), range)];
        let people: Vec<Person> = Type::from_chunks(people).unwrap();
        assert_eq!(people.len(), 3);

        assert_eq!(people[0].name, "Gutenberg");
        assert_eq!(people[0].prefix, "and");
        assert_eq!(people[0].given_name, "Johannes");
    }

    #[test]
    fn test_trailing_and() {
        let names = String::from(
            "Johannes Gutenberg and
Aldus Manutius and
Claude Garamond and",
        );
        let range = std::ops::Range { start: 0, end: names.len() };
        let people = &[Spanned::new(Chunk::Normal(names), range)];
        let people: Vec<Person> = Type::from_chunks(people).unwrap();
        assert_eq!(people.len(), 3);

        assert_eq!(people[2].name, "and");
        assert_eq!(people[2].prefix, "");
        assert_eq!(people[2].given_name, "Claude Garamond");
    }

    #[test]
    fn test_consecutive_and() {
        let names = String::from(
            "Johannes Gutenberg and and
Aldus Manutius and
Claude Garamond",
        );
        let range = std::ops::Range { start: 0, end: names.len() };
        let people = &[Spanned::new(Chunk::Normal(names), range)];
        let people: Vec<Person> = Type::from_chunks(people).unwrap();
        assert_eq!(people.len(), 4);

        assert_eq!(people[1].name, "");
        assert_eq!(people[1].prefix, "");
        assert_eq!(people[1].given_name, "");

        let names = String::from(
            "Johannes Gutenberg and and and
Aldus Manutius and
Claude Garamond",
        );
        let range = std::ops::Range { start: 0, end: names.len() };
        let people = &[Spanned::new(Chunk::Normal(names), range)];
        let people: Vec<Person> = Type::from_chunks(people).unwrap();
        assert_eq!(people.len(), 5);

        assert_eq!(people[1].name, "");
        assert_eq!(people[1].prefix, "");
        assert_eq!(people[1].given_name, "");
        assert_eq!(people[2].name, "");
        assert_eq!(people[2].prefix, "");
        assert_eq!(people[2].given_name, "");
    }

    #[test]
    fn test_name_with_and_inside() {
        let names = String::from(
            "Johannes anderson Gutenberg and Claudeand Garamond and Aanderson Manutius",
        );
        let range = std::ops::Range { start: 0, end: names.len() };
        let people = &[Spanned::new(Chunk::Normal(names), range)];
        let people: Vec<Person> = Type::from_chunks(people).unwrap();
        assert_eq!(people.len(), 3);

        assert_eq!(people[0].name, "Gutenberg");
        assert_eq!(people[0].prefix, "anderson");
        assert_eq!(people[0].given_name, "Johannes");

        assert_eq!(people[1].name, "Garamond");
        assert_eq!(people[1].prefix, "");
        assert_eq!(people[1].given_name, "Claudeand");

        assert_eq!(people[2].name, "Manutius");
        assert_eq!(people[2].prefix, "");
        assert_eq!(people[2].given_name, "Aanderson");
    }

    #[test]
    fn test_person_comma() {
        let p = Person::parse(&[Spanned::zero(N("jean de la fontaine,"))]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "jean de la");
        assert_eq!(p.given_name, "");
        assert_eq!(vec![p].to_chunks(), vec![d(N("jean de la fontaine, "),)]);

        let p = Person::parse(&[Spanned::zero(N("de la fontaine, Jean"))]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "de la");
        assert_eq!(p.given_name, "Jean");
        assert_eq!(vec![p].to_chunks(), vec![d(N("de la fontaine, Jean"),)]);

        let p = Person::parse(&[Spanned::zero(N("De La Fontaine, Jean"))]);
        assert_eq!(p.name, "De La Fontaine");
        assert_eq!(p.prefix, "");
        assert_eq!(p.given_name, "Jean");
        assert_eq!(vec![p].to_chunks(), vec![d(N("De La Fontaine, Jean"),)]);

        let p = Person::parse(&[s(V("De La"), 2..6), s(N(" Fontaine, Jean"), 7..15)]);
        assert_eq!(p.name, "Fontaine");
        assert_eq!(p.prefix, "De La");
        assert_eq!(p.given_name, "Jean");
        assert_eq!(vec![p].to_chunks(), vec![d(V("De La")), d(N(" Fontaine, Jean"))]);

        let p = Person::parse(&[Spanned::zero(N("De la Fontaine, Jean"))]);
        assert_eq!(p.name, "Fontaine");
        assert_eq!(p.prefix, "De la");
        assert_eq!(p.given_name, "Jean");

        let p = Person::parse(&[Spanned::zero(N("de La Fontaine, Jean"))]);
        assert_eq!(p.name, "La Fontaine");
        assert_eq!(p.prefix, "de");
        assert_eq!(p.given_name, "Jean");
    }

    #[test]
    fn test_person_no_comma() {
        let p = Person::parse(&[Spanned::zero(N(""))]);
        assert_eq!(p.name, "");
        assert_eq!(p.prefix, "");
        assert_eq!(p.given_name, "");

        let p = Person::parse(&[Spanned::zero(N("jean de la fontaine"))]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "jean de la");
        assert_eq!(p.given_name, "");

        let p = Person::parse(&[Spanned::zero(N("Jean de la fontaine"))]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "de la");
        assert_eq!(p.given_name, "Jean");

        let p = Person::parse(&[
            Spanned::zero(N("Jean ")),
            Spanned::zero(V("de")),
            Spanned::zero(N(" la fontaine")),
        ]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "la");
        assert_eq!(p.given_name, "Jean de");

        let p = Person::parse(&[
            Spanned::zero(N("Jean ")),
            Spanned::zero(V("de")),
            Spanned::zero(N(" ")),
            Spanned::zero(V("la")),
            Spanned::zero(N(" fontaine")),
        ]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "");
        assert_eq!(p.given_name, "Jean de la");

        let p = Person::parse(&[
            Spanned::zero(N("jean ")),
            Spanned::zero(V("de")),
            Spanned::zero(N(" ")),
            Spanned::zero(V("la")),
            Spanned::zero(N(" fontaine")),
        ]);
        assert_eq!(p.name, "de la fontaine");
        assert_eq!(p.prefix, "jean");
        assert_eq!(p.given_name, "");

        let p = Person::parse(&[Spanned::zero(N("Jean De La Fontaine"))]);
        assert_eq!(p.name, "Fontaine");
        assert_eq!(p.prefix, "");
        assert_eq!(p.given_name, "Jean De La");

        let p = Person::parse(&[Spanned::zero(N("jean De la Fontaine"))]);
        assert_eq!(p.name, "Fontaine");
        assert_eq!(p.prefix, "jean De la");
        assert_eq!(p.given_name, "");

        let p = Person::parse(&[Spanned::zero(N("Jean de La Fontaine"))]);
        assert_eq!(p.name, "La Fontaine");
        assert_eq!(p.prefix, "de");
        assert_eq!(p.given_name, "Jean");
    }

    #[test]
    fn test_person_two_comma() {
        let p = Person::parse(&[Spanned::zero(N("Mudd, Sr., Harcourt Fenton"))]);
        assert_eq!(p.name, "Mudd");
        assert_eq!(p.prefix, "");
        assert_eq!(p.suffix, "Sr.");
        assert_eq!(p.given_name, "Harcourt Fenton");
    }
}
