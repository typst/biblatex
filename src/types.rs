//! A collection of strong field types parsable from chunks.

use std::cmp::Ordering;
use std::fmt;
use std::ops::Range;
use std::str::FromStr;

use anyhow::anyhow;
use chinese_number::{ChineseNumberCountMethod, ChineseNumberToNumber};
use chrono::{Datelike, NaiveDate, NaiveTime};
use lazy_static::lazy_static;
use numerals::roman::Roman;
use regex::Regex;
use strum_macros::{AsRefStr, Display, EnumString};

use super::{Chunk, ChunksExt};

#[rustfmt::skip]
lazy_static! {
    // Range regex (like `5 -- 7`).
    static ref RANGE_REGEX: Regex = Regex::new(r"(?P<s>\d+)\s*-+\s*(\d+:)?(?P<e>\d+)").unwrap();

    // Definite (i.e. non-range) date regexes.
    static ref MONTH_REGEX: Regex = Regex::new(r"^(?P<y>(\+|-)?\s*\d{4})-+(?P<m>\d{2})").unwrap();
    static ref YEAR_REGEX: Regex = Regex::new(r"^(?P<y>(\+|-)?\s*\d{4})").unwrap();

    // Date range regexes.
    static ref CENTURY_REGEX: Regex = Regex::new(r"^(?P<y>(\+|-)?\d{2})XX").unwrap();
    static ref DECADE_REGEX: Regex = Regex::new(r"^(?P<y>(\+|-)?\d{3})X").unwrap();
    static ref MONTH_UNSURE_REGEX: Regex = Regex::new(r"^(?P<y>(\+|-)?\s*\d{4})-+XX").unwrap();
    static ref DAY_UNSURE_REGEX: Regex = Regex::new(r"^(?P<y>(\+|-)?\s*\d{4})-*(?P<m>\d{2})-*XX").unwrap();
    static ref DAY_MONTH_UNSURE_REGEX: Regex = Regex::new(r"^(?P<y>(\+|-)?\s*\d{4})-*XX-*XX").unwrap();

    // Date part Regexes
    static ref MONTH_PART_REGEX: Regex = Regex::new(r"^\s*(?P<m>\w+)").unwrap();
    static ref MONTH_DAY_PART_REGEX: Regex = Regex::new(r"^\s*(?P<m>\w+)(-|\u{00a0}|\s)+(?P<d>[0-9]+)").unwrap();
}

// *********************************** Name Parsing *********************************** //

/// An author, editor, or some other person affiliated with the cited work.
/// When obtained through the constructor `Person::new`, the fields are trimmed.
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
    /// Constructs a new Person from a chunk vector according to the specs of
    /// [Nicolas Markey in "Tame the BeaST"][taming], pp. 23-24.
    ///
    /// [taming]: https://ftp.rrze.uni-erlangen.de/ctan/info/bibtex/tamethebeast/ttb_en.pdf
    pub fn new(source: &[Chunk]) -> Self {
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
            0 => Self::from_unified(&source),
            1 => {
                let (v1, v2) = split_at_normal_char(source, ',', true);
                Self::from_single_comma(&v1, &v2)
            }
            _ => {
                let (v1, v2) = split_at_normal_char(source, ',', true);
                let (v2, v3) = split_at_normal_char(&v2, ',', true);
                Self::from_two_commas(&v1, &v2, &v3)
            }
        }
    }

    /// Constructs new person from a chunk slice if in the
    /// form `<First> <Prefix> <Last>`.
    fn from_unified(source: &[Chunk]) -> Self {
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

        for (index, (c, v)) in chunk_chars(&source).enumerate() {
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

        for (index, (c, _)) in chunk_chars(&source).enumerate() {
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
    fn from_single_comma(s1: &[Chunk], s2: &[Chunk]) -> Self {
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
    fn from_two_commas(s1: &[Chunk], s2: &[Chunk], s3: &[Chunk]) -> Self {
        let mut p = Self::from_single_comma(s1, s3);
        p.suffix = s2.format_verbatim();
        p
    }
}

impl fmt::Display for Person {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
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

// *********************************** Date Parsing *********************************** //

/// Represents a date or a range of dates and their certainty and exactness.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Date {
    /// Indicates whether the sources are sure about the date.
    pub is_uncertain: bool,
    /// Indicates the specificity of the date value.
    pub is_approximate: bool,
    /// The date or the date range.
    pub value: DateValue,
}

/// Represents a atomic date or a range of dates.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum DateValue {
    /// A single date.
    Atom(DateAtom),
    /// A range of dates that may be open or definite at both start and end.
    Range(DateBound, DateBound),
}

/// Indicates whether the start or end of a date interval is open or definite.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum DateBound {
    /// The start or end of the range is open / unknown.
    Open,
    /// The start or end of the range is definite / known.
    Definite(DateAtom),
}

/// A date atom is a timezone-unaware date that must specify a year
/// and may specify month, day, and time. Flags about uncertainity / precision
/// are stored within the parent `Date` struct.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct DateAtom {
    /// The year.
    ///
    /// AD years are counted starting from one and thus represented as exactly their year
    /// (e.g. 2000 AD is `2000`) whereas BC years are counted starting from zero downwards
    /// (e.g. 1000 BC is `999`)
    pub year: i32,
    /// The month (starting at zero).
    pub month: Option<u8>,
    /// The day (starting at zero).
    pub day: Option<u8>,
    /// The timezone-unaware time.
    pub time: Option<NaiveTime>,
}

impl Date {
    /// Create a new date from a chunk vector.
    pub fn new(chunks: &[Chunk]) -> anyhow::Result<Self> {
        let mut date_str = chunks.format_verbatim().trim_end().to_string();

        let last_char = date_str.chars().last().ok_or(anyhow!("Date string is empty"))?;
        let (is_uncertain, is_approximate) = match last_char {
            '?' => (true, false),
            '~' => (false, true),
            '%' => (true, true),
            _ => (false, false),
        };

        let value = if date_str.to_uppercase().contains('X') {
            let (d1, d2) = Self::range_dates(date_str)?;
            DateValue::Range(DateBound::Definite(d1), DateBound::Definite(d2))
        } else {
            if date_str.contains('/') {
                let (s1, s2) = split_at_normal_char(chunks, '/', true);
                let (s1, mut s2) = (s1.format_verbatim(), s2.format_verbatim());

                if is_uncertain || is_approximate {
                    s2.pop();
                }

                let start = if Self::is_open_range(&s1) {
                    DateBound::Open
                } else {
                    DateBound::Definite(DateAtom::new(s1)?)
                };

                let end = if Self::is_open_range(&s2) {
                    DateBound::Open
                } else {
                    DateBound::Definite(DateAtom::new(s2)?)
                };

                DateValue::Range(start, end)
            } else {
                if is_uncertain || is_approximate {
                    date_str.pop();
                }

                DateValue::Atom(DateAtom::new(date_str)?)
            }
        };

        Ok(Self { is_approximate, is_uncertain, value })
    }

    pub fn new_from_three_fields(
        year: Option<&[Chunk]>,
        month: Option<&[Chunk]>,
        day: Option<&[Chunk]>,
    ) -> Result<Self, anyhow::Error> {
        let mut year = year
            .ok_or_else(|| anyhow!("Year field must be set"))?
            .format_verbatim();

        year.retain(|c| !c.is_whitespace());

        let capt = YEAR_REGEX.captures(&year).ok_or(anyhow!("Invalid year data"))?;
        let year: i32 = capt.name("y").unwrap().as_str().parse().unwrap();
        let mut date_atom = DateAtom { year, month: None, day: None, time: None };

        if let Some(month) = month {
            let month = month.format_verbatim();
            if let Some(day) = day {
                let mut day = day.format_verbatim();
                day.retain(|c| !c.is_whitespace());
                let day: u8 = day.parse()?;

                if day > 31 || day < 1 {
                    return Err(anyhow!("Day not within range"));
                }
                date_atom.day = Some(day - 1);

                let capt = MONTH_PART_REGEX.captures(&month);
                if let Some(capt) = capt {
                    let name = capt.name("m").unwrap().as_str();
                    date_atom.month = get_month_for_name(name)
                        .or_else(|| get_month_for_abbr(name).map(|x| x.1));
                }
            } else if let Some(capt) = MONTH_DAY_PART_REGEX.captures(&month) {
                let name = capt.name("m").unwrap().as_str();
                date_atom.month = get_month_for_name(name)
                    .or_else(|| get_month_for_abbr(name).map(|x| x.1));
                if date_atom.month.is_some() {
                    let day: u8 = capt.name("d").unwrap().as_str().parse().unwrap();

                    if day > 31 || day < 1 {
                        return Err(anyhow!("Day not within range"));
                    }
                    date_atom.day = Some(day - 1);
                }
            } else if let Some(capt) = MONTH_PART_REGEX.captures(&month) {
                let name = capt.name("m").unwrap().as_str();
                date_atom.month = get_month_for_name(name)
                    .or_else(|| get_month_for_abbr(name).map(|x| x.1));
            }
        }

        Ok(Date::new_from_date_atom(date_atom))
    }

    fn new_from_date_atom(atom: DateAtom) -> Self {
        Date {
            is_approximate: false,
            is_uncertain: false,
            value: DateValue::Atom(atom),
        }
    }

    fn is_open_range(s: &str) -> bool {
        if s.trim().is_empty() {
            true
        } else if s.trim() == ".." {
            true
        } else {
            false
        }
    }

    fn range_dates(mut source: String) -> anyhow::Result<(DateAtom, DateAtom)> {
        source.retain(|c| !c.is_whitespace());

        if let Some(captures) = CENTURY_REGEX.captures(&source) {
            let century: i32 = (captures.name("y").unwrap()).as_str().parse().unwrap();
            Ok((
                DateAtom {
                    year: century * 100,
                    month: None,
                    day: None,
                    time: None,
                },
                DateAtom {
                    year: century * 100 + 99,
                    month: None,
                    day: None,
                    time: None,
                },
            ))
        } else if let Some(captures) = DECADE_REGEX.captures(&source) {
            let decade: i32 = (captures.name("y").unwrap()).as_str().parse().unwrap();
            Ok((
                DateAtom {
                    year: decade * 10,
                    month: None,
                    day: None,
                    time: None,
                },
                DateAtom {
                    year: decade * 10 + 9,
                    month: None,
                    day: None,
                    time: None,
                },
            ))
        } else if let Some(captures) = MONTH_UNSURE_REGEX.captures(&source) {
            let year = (captures.name("y").unwrap()).as_str().parse().unwrap();

            Ok((
                DateAtom {
                    year,
                    month: Some(0),
                    day: None,
                    time: None,
                },
                DateAtom {
                    year,
                    month: Some(11),
                    day: None,
                    time: None,
                },
            ))
        } else if let Some(captures) = DAY_MONTH_UNSURE_REGEX.captures(&source) {
            let year = (captures.name("y").unwrap()).as_str().parse().unwrap();

            Ok((
                DateAtom {
                    year,
                    month: Some(0),
                    day: Some(0),
                    time: None,
                },
                DateAtom {
                    year,
                    month: Some(11),
                    day: Some(30),
                    time: None,
                },
            ))
        } else if let Some(captures) = DAY_UNSURE_REGEX.captures(&source) {
            let year = (captures.name("y").unwrap()).as_str().parse().unwrap();
            let month = (captures.name("m").unwrap()).as_str().parse::<u8>().unwrap();

            let days = if month == 12 {
                NaiveDate::from_ymd(year + 1, 1, 1)
            } else {
                NaiveDate::from_ymd(year, month as u32 + 1, 1)
            }
            .signed_duration_since(NaiveDate::from_ymd(year, month as u32, 1))
            .num_days();

            Ok((
                DateAtom {
                    year,
                    month: Some(month - 1),
                    day: Some(0),
                    time: None,
                },
                DateAtom {
                    year,
                    month: Some(month - 1),
                    day: Some(days as u8 - 1),
                    time: None,
                },
            ))
        } else {
            Err(anyhow!("Date does not match any known format"))
        }
    }
}

/// Used to resolve month abbreviations to their respective values.
pub(crate) fn get_month_for_abbr(month: &str) -> Option<(String, u8)> {
    match month.to_lowercase().as_str() {
        "jan" => Some(("January".to_string(), 0)),
        "feb" => Some(("February".to_string(), 1)),
        "mar" => Some(("March".to_string(), 2)),
        "apr" => Some(("April".to_string(), 3)),
        "may" => Some(("May".to_string(), 4)),
        "jun" => Some(("June".to_string(), 5)),
        "jul" => Some(("July".to_string(), 6)),
        "aug" => Some(("August".to_string(), 7)),
        "sep" => Some(("September".to_string(), 8)),
        "oct" => Some(("October".to_string(), 9)),
        "nov" => Some(("November".to_string(), 10)),
        "dec" => Some(("December".to_string(), 11)),
        _ => None,
    }
}

/// Used to resolve month names to their respective values.
fn get_month_for_name(month: &str) -> Option<u8> {
    match month.to_lowercase().as_str() {
        "january" => Some(0),
        "february" => Some(1),
        "march" => Some(2),
        "april" => Some(3),
        "may" => Some(4),
        "june" => Some(5),
        "july" => Some(6),
        "august" => Some(7),
        "september" => Some(8),
        "october" => Some(9),
        "november" => Some(10),
        "december" => Some(11),
        _ => None,
    }
}

// TODO: Handle open date kind
// impl PartialOrd for Date {
//     fn partial_cmp(&self, other: &Date) -> Option<Ordering> {
//         if let Some(range_end) = &self.range_end {
//             if let Some(range_end_o) = &other.range_end {
//                 let start_cmp = self.value.partial_cmp(&other.value);
//                 let end_cmp = range_end.partial_cmp(&range_end_o);
//                 if start_cmp.is_none() || end_cmp.is_none() {
//                     return None;
//                 }

//                 let start_cmp = start_cmp.unwrap();
//                 let end_cmp = end_cmp.unwrap();

//                 if start_cmp == end_cmp || end_cmp == Ordering::Equal {
//                     Some(start_cmp)
//                 } else if start_cmp == Ordering::Equal {
//                     Some(end_cmp)
//                 } else {
//                     None
//                 }
//             } else {
//                 self.value.partial_cmp(&other.value)
//             }
//         } else {
//             // We do not have it
//             if other.range_end.is_none() {
//                 self.value.partial_cmp(&other.value)
//             } else {
//                 // Use the above implementation
//                 other.partial_cmp(self).map(Ordering::reverse)
//             }
//         }
//     }
// }

impl DateAtom {
    /// Parse a date atom from a string.
    pub fn new(mut source: String) -> anyhow::Result<Self> {
        source.retain(|f| !f.is_whitespace());

        let time = if let Some(pos) = source.find('T') {
            if pos + 1 < source.len() {
                let time_str = source.split_off(pos + 1);
                source.pop();
                time_str.parse::<NaiveTime>().ok()
            } else {
                None
            }
        } else {
            None
        };

        let full_date = source.parse::<NaiveDate>();

        if let Ok(ndate) = full_date {
            Ok(DateAtom {
                year: ndate.year(),
                month: Some(ndate.month0() as u8),
                day: Some(ndate.day0() as u8),
                time,
            })
        } else if let Some(captures) = MONTH_REGEX.captures(&source) {
            Ok(DateAtom {
                year: (captures.name("y").unwrap()).as_str().parse().unwrap(),
                month: Some(
                    (captures.name("m").unwrap()).as_str().parse::<u8>().unwrap() - 1,
                ),
                day: None,
                time,
            })
        } else if let Some(captures) = YEAR_REGEX.captures(&source) {
            Ok(DateAtom {
                year: (captures.name("y").unwrap()).as_str().parse().unwrap(),
                month: None,
                day: None,
                time,
            })
        } else {
            Err(anyhow!("Date does not match any known format"))
        }
    }
}

impl PartialOrd for DateAtom {
    fn partial_cmp(&self, other: &DateAtom) -> Option<Ordering> {
        let year_ord = self.year.cmp(&other.year);
        if year_ord != Ordering::Equal {
            return Some(year_ord);
        }

        match (self.month, other.month) {
            (Some(s), Some(o)) => {
                let month_ord = s.cmp(&o);
                if month_ord != Ordering::Equal {
                    return Some(month_ord);
                }
            }
            (None, None) => return Some(Ordering::Equal),
            _ => return None,
        }

        match (self.day, other.day) {
            (Some(s), Some(o)) => {
                let day_ord = s.cmp(&o);
                if day_ord != Ordering::Equal {
                    return Some(day_ord);
                }
            }
            (None, None) => return Some(Ordering::Equal),
            _ => return None,
        }

        match (self.time, other.time) {
            (Some(s), Some(o)) => Some(s.cmp(&o)),
            (None, None) => Some(Ordering::Equal),
            _ => None,
        }
    }
}

// *************************** Chunk Type Parsing Adaptors **************************** //

/// Trait for deserializing Bib(La)TeX data types from chunk slices.
pub trait Type: Sized {
    /// Allows to interpret data from a resolved chunk slices as a type.
    fn parse(chunks: &[Chunk]) -> anyhow::Result<Self>;
}

impl Type for Vec<Vec<Chunk>> {
    /// Splits the chunks at `"and"`s.
    fn parse(chunks: &[Chunk]) -> anyhow::Result<Self> {
        Ok(split_token_lists(chunks, "and"))
    }
}

impl Type for Vec<Person> {
    fn parse(chunks: &[Chunk]) -> anyhow::Result<Self> {
        Ok(chunks
            .parse::<Vec<Vec<Chunk>>>()?
            .into_iter()
            .map(|subchunks| Person::new(&subchunks))
            .collect())
    }
}

impl Type for Date {
    fn parse(chunks: &[Chunk]) -> anyhow::Result<Self> {
        Date::new(chunks)
    }
}

impl Type for String {
    fn parse(chunks: &[Chunk]) -> anyhow::Result<Self> {
        Ok(chunks.format_verbatim())
    }
}

impl Type for i64 {
    fn parse(chunks: &[Chunk]) -> anyhow::Result<Self> {
        parse_integers(chunks)
    }
}

impl Type for IntOrChunks {
    fn parse(chunks: &[Chunk]) -> anyhow::Result<Self> {
        if let Ok(int) = parse_integers(chunks) {
            Ok(IntOrChunks::Int(int))
        } else {
            Ok(IntOrChunks::Chunks(chunks.to_vec()))
        }
    }
}

impl Type for Range<u32> {
    fn parse(chunks: &[Chunk]) -> anyhow::Result<Self> {
        if let Some(range) = parse_ranges(chunks).into_iter().next() {
            Ok(range)
        } else {
            Err(anyhow!("No range specified"))
        }
    }
}

impl Type for Vec<Range<u32>> {
    fn parse(chunks: &[Chunk]) -> anyhow::Result<Self> {
        Ok(parse_ranges(chunks))
    }
}

impl Type for Pagination {
    fn parse(chunks: &[Chunk]) -> anyhow::Result<Self> {
        Ok(Pagination::from_str(
            &chunks.format_verbatim().to_lowercase(),
        )?)
    }
}

impl Type for EditorType {
    fn parse(chunks: &[Chunk]) -> anyhow::Result<Self> {
        Ok(EditorType::from_str(
            &chunks.format_verbatim().to_lowercase(),
        )?)
    }
}

impl Type for Gender {
    fn parse(chunks: &[Chunk]) -> anyhow::Result<Self> {
        Gender::from_str(&chunks.format_verbatim().to_lowercase())
    }
}

// ********************************** Range Parsing *********************************** //

/// Parse range fields with a number of ranges and an amount of dashes seperating
/// start from end.
fn parse_ranges(source: &[Chunk]) -> Vec<Range<u32>> {
    let range_vecs = split_token_lists(source, ",");

    let mut res = vec![];
    for range_candidate in range_vecs.iter().map(|f| f.format_verbatim()) {
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

// ********************************* Integer Parsing ********************************** //

/// An integer or a chunk vector.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum IntOrChunks {
    Int(i64),
    Chunks(Vec<Chunk>),
}

/// Parse integers. This method will accept arabic, roman, and chinese numerals.
fn parse_integers(source: &[Chunk]) -> anyhow::Result<i64> {
    let s = source.format_verbatim();
    let s = s.trim();

    if let Ok(n) = str::parse::<i64>(s) {
        Ok(n)
    } else if let Some(roman) = Roman::parse(s) {
        Ok(roman.value() as i64)
    } else if let Ok(n) = s.parse_chinese_number(ChineseNumberCountMethod::TenThousand) {
        Ok(n)
    } else {
        Err(anyhow!("Could not parse integer"))
    }
}

// ********************************** Various enums *********************************** //

/// Defines the pagination scheme to use for formatting purposes.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Display, EnumString, AsRefStr)]
#[strum(serialize_all = "snake_case")]
pub enum Pagination {
    Page,
    Column,
    Line,
    Verse,
    Section,
    Paragraph,
}

/// Which role the according editor had (cf. EditorA, EditorB, EditorC fields).
#[derive(Debug, Copy, Clone, Eq, PartialEq, Display, EnumString, AsRefStr)]
#[strum(serialize_all = "snake_case")]
pub enum EditorType {
    Editor,
    Compiler,
    Founder,
    Continuator,
    Redactor,
    Reviser,
    Collaborator,
    Organizer,
}

/// Gender of the author or editor (if no author specified).
#[derive(Debug, Copy, Clone, Eq, PartialEq, Display, AsRefStr)]
pub enum Gender {
    SingularFemale,
    SingularMale,
    SingularNeuter,
    PluralFemale,
    PluralMale,
    PluralNeuter,
}

impl FromStr for Gender {
    type Err = anyhow::Error;

    /// Two-letter gender serialization in accordance with the BibLaTeX standard.
    fn from_str(s: &str) -> Result<Gender, Self::Err> {
        match s {
            "sf" => Ok(Gender::SingularFemale),
            "sm" => Ok(Gender::SingularMale),
            "sn" => Ok(Gender::SingularNeuter),
            "pf" => Ok(Gender::PluralFemale),
            "pm" => Ok(Gender::PluralMale),
            "pn" => Ok(Gender::PluralNeuter),
            _ => Err(anyhow!("Unknown gender identifier")),
        }
    }
}

impl Gender {
    /// Puts the gender into plural.
    pub fn pluralize(self) -> Self {
        match self {
            Gender::SingularFemale => Gender::PluralFemale,
            Gender::SingularMale => Gender::PluralMale,
            Gender::SingularNeuter => Gender::PluralNeuter,
            _ => self,
        }
    }

    /// Puts the gender into the singular.
    pub fn singularize(self) -> Self {
        match self {
            Gender::PluralFemale => Gender::SingularFemale,
            Gender::PluralMale => Gender::SingularMale,
            Gender::PluralNeuter => Gender::SingularNeuter,
            _ => self,
        }
    }

    /// Finds a gender to summarize a list of genders.
    pub fn coalesce(list: &[Self]) -> Option<Self> {
        if list.is_empty() {
            return None;
        }

        if list.len() == 1 {
            return Some(list[0]);
        }

        let mut was_female = false;
        let mut was_male = false;
        let mut was_neuter = false;

        for g in list {
            match g {
                Self::SingularFemale | Gender::PluralFemale => was_female = true,
                Self::SingularMale | Self::PluralMale => was_male = true,
                Self::SingularNeuter | Self::PluralNeuter => was_neuter = true,
            }
        }

        if was_female && !was_male && !was_neuter {
            Some(Gender::PluralFemale)
        } else if !was_female && was_male && !was_neuter {
            Some(Gender::PluralMale)
        } else {
            Some(Gender::PluralNeuter)
        }
    }
}

// ************************************ Utilities ************************************* //

/// Splits chunk vectors that are a token lists as defined per the
/// [BibLaTeX Manual][manual] p. 16 along occurances of the keyword.
///
/// [manual]: http://ctan.ebinger.cc/tex-archive/macros/latex/contrib/biblatex/doc/biblatex.pdf
fn split_token_lists(vals: &[Chunk], keyword: &str) -> Vec<Vec<Chunk>> {
    let mut out = vec![];
    let mut latest = vec![];

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
            latest.push(val.clone());
        }
    }

    out.push(latest);
    out
}

/// Splits a chunk vector into two at the first occurrance of the character `c`.
/// `omit` controls whether the output will contain `c`.
fn split_at_normal_char(src: &[Chunk], c: char, omit: bool) -> (Vec<Chunk>, Vec<Chunk>) {
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
fn split_values(src: &[Chunk], vi: usize, si: usize) -> (Vec<Chunk>, Vec<Chunk>) {
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

/// An iterator over the characters in each chunk, indicating whether they are verbatim or
/// not. Chunk types other than `Normal` or `Verbatim` are ommitted.
fn chunk_chars<'a>(chunks: &'a [Chunk]) -> impl Iterator<Item = (char, bool)> + 'a {
    chunks.iter().flat_map(|chunk| {
        let (s, verbatim) = match chunk {
            Chunk::Normal(s) => (s, false),
            Chunk::Verbatim(s) => (s, true),
        };

        s.chars().map(move |c| (c, verbatim))
    })
}

#[cfg(test)]
#[allow(non_snake_case)]
mod tests {
    use chrono::NaiveTime;

    use super::*;
    use DateBound::Definite;

    fn N(s: &str) -> Chunk {
        Chunk::Normal(s.to_string())
    }
    fn V(s: &str) -> Chunk {
        Chunk::Verbatim(s.to_string())
    }

    #[test]
    fn test_value_iterator() {
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
    fn test_value_split() {
        let vls = &[N("split "), V("exac^tly"), N("here")];
        let ref1 = &[N("split "), V("exac^")];
        let ref2 = &[V("tly"), N("here")];
        let split = split_values(vls, 1, 5);
        assert_eq!(split.0, ref1);
        assert_eq!(split.1, ref2);
    }

    #[test]
    fn test_person_comma() {
        let p = Person::new(&[N("jean de la fontaine,")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "jean de la");
        assert_eq!(p.given_name, "");

        let p = Person::new(&[N("de la fontaine, Jean")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "de la");
        assert_eq!(p.given_name, "Jean");

        let p = Person::new(&[N("De La Fontaine, Jean")]);
        assert_eq!(p.name, "De La Fontaine");
        assert_eq!(p.prefix, "");
        assert_eq!(p.given_name, "Jean");

        let p = Person::new(&[N("De la Fontaine, Jean")]);
        assert_eq!(p.name, "Fontaine");
        assert_eq!(p.prefix, "De la");
        assert_eq!(p.given_name, "Jean");

        let p = Person::new(&[N("de La Fontaine, Jean")]);
        assert_eq!(p.name, "La Fontaine");
        assert_eq!(p.prefix, "de");
        assert_eq!(p.given_name, "Jean");
    }

    #[test]
    fn test_person_no_comma() {
        let p = Person::new(&[N("jean de la fontaine")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "jean de la");
        assert_eq!(p.given_name, "");

        let p = Person::new(&[N("Jean de la fontaine")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "de la");
        assert_eq!(p.given_name, "Jean");

        let p = Person::new(&[N("Jean "), V("de"), N(" la fontaine")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "la");
        assert_eq!(p.given_name, "Jean de");

        let p = Person::new(&[N("Jean "), V("de"), N(" "), V("la"), N(" fontaine")]);
        assert_eq!(p.name, "fontaine");
        assert_eq!(p.prefix, "");
        assert_eq!(p.given_name, "Jean de la");

        let p = Person::new(&[N("jean "), V("de"), N(" "), V("la"), N(" fontaine")]);
        assert_eq!(p.name, "de la fontaine");
        assert_eq!(p.prefix, "jean");
        assert_eq!(p.given_name, "");

        let p = Person::new(&[N("Jean De La Fontaine")]);
        assert_eq!(p.name, "Fontaine");
        assert_eq!(p.prefix, "");
        assert_eq!(p.given_name, "Jean De La");

        let p = Person::new(&[N("jean De la Fontaine")]);
        assert_eq!(p.name, "Fontaine");
        assert_eq!(p.prefix, "jean De la");
        assert_eq!(p.given_name, "");

        let p = Person::new(&[N("Jean de La Fontaine")]);
        assert_eq!(p.name, "La Fontaine");
        assert_eq!(p.prefix, "de");
        assert_eq!(p.given_name, "Jean");

        let p = Person::new(&[N("")]);
        assert_eq!(p.name, "");
        assert_eq!(p.prefix, "");
        assert_eq!(p.given_name, "");
    }

    #[test]
    fn test_person_two_comma() {
        let p = Person::new(&[N("Mudd, Sr., Harcourt Fenton")]);
        assert_eq!(p.name, "Mudd");
        assert_eq!(p.prefix, "");
        assert_eq!(p.suffix, "Sr.");
        assert_eq!(p.given_name, "Harcourt Fenton");
    }

    #[test]
    fn test_value_split_at_normal_char() {
        let vls = &[N("split "), V("not, "), N("but rather, here")];
        let ref1 = &[N("split "), V("not, "), N("but rather")];
        let ref2 = &[N("here")];
        let split = split_at_normal_char(vls, ',', true);
        assert_eq!(split.0, ref1);
        assert_eq!(split.1, ref2);
    }

    #[test]
    fn test_ranges() {
        let ranges = &[N("31--43,21:4-21:6,  194 --- 245")];
        let res = parse_ranges(ranges);
        assert_eq!(res[0], 31 .. 43);
        assert_eq!(res[1], 4 .. 6);
        assert_eq!(res[2], 194 .. 245);
    }

    #[test]
    fn test_new_date_atom() {
        let atom1 = DateAtom::new("2017-10 -25".to_string()).unwrap();
        assert_eq!(atom1.year, 2017);
        assert_eq!(atom1.month, Some(9));
        assert_eq!(atom1.day, Some(24));
        assert_eq!(atom1.time, None);

        let atom2 = DateAtom::new("  2019 -- 03 ".to_string()).unwrap();
        assert_eq!(atom2.year, 2019);
        assert_eq!(atom2.month, Some(2));
        assert_eq!(atom2.day, None);
        assert_eq!(atom2.time, None);

        let atom3 = DateAtom::new("  -0006".to_string()).unwrap();
        assert_eq!(atom3.year, -6);
        assert_eq!(atom3.month, None);
        assert_eq!(atom3.day, None);
        assert_eq!(atom3.time, None);

        let atom4 = DateAtom::new("2020-09-06T13:39:00".to_string()).unwrap();
        assert_eq!(atom4.year, 2020);
        assert_eq!(atom4.month, Some(8));
        assert_eq!(atom4.day, Some(5));
        assert_eq!(atom4.time, Some(NaiveTime::from_hms(13, 39, 00)));

        assert!(atom3 < atom4);
        assert!(atom2 > atom1);
    }

    #[test]
    fn test_new_date() {
        let date = Date::new(&[N("2017-10 -25?")]).unwrap();
        assert_eq!(date.is_uncertain, true);
        assert_eq!(date.is_approximate, false);
        if let DateValue::Atom(val) = date.value {
            assert_eq!(val.year, 2017);
            assert_eq!(val.month, Some(9));
            assert_eq!(val.day, Some(24));
            assert_eq!(val.time, None);
        } else {
            panic!("wrong date kind");
        }

        let date = Date::new(&[N("19XX~")]).unwrap();
        assert_eq!(date.is_uncertain, false);
        assert_eq!(date.is_approximate, true);
        if let DateValue::Range(Definite(start), Definite(end)) = date.value {
            assert_eq!(start.year, 1900);
            assert_eq!(start.month, None);
            assert_eq!(start.day, None);
            assert_eq!(start.time, None);

            assert_eq!(end.year, 1999);
            assert_eq!(end.month, None);
            assert_eq!(end.day, None);
            assert_eq!(end.time, None);
        } else {
            panic!("wrong date kind");
        }

        let date = Date::new(&[N("1948-03-02/1950")]).unwrap();
        assert_eq!(date.is_uncertain, false);
        assert_eq!(date.is_approximate, false);
        if let DateValue::Range(Definite(start), Definite(end)) = date.value {
            assert_eq!(start.year, 1948);
            assert_eq!(start.month, Some(2));
            assert_eq!(start.day, Some(1));
            assert_eq!(start.time, None);

            assert_eq!(end.year, 1950);
            assert_eq!(end.month, None);
            assert_eq!(end.day, None);
            assert_eq!(end.time, None);
        } else {
            panic!("wrong date kind");
        }

        let date = Date::new(&[N("2020-04-04T18:30:31/")]).unwrap();
        assert_eq!(date.is_uncertain, false);
        assert_eq!(date.is_approximate, false);
        if let DateValue::Range(Definite(start), DateBound::Open) = date.value {
            assert_eq!(start.year, 2020);
            assert_eq!(start.month, Some(3));
            assert_eq!(start.day, Some(3));
            assert_eq!(start.time, Some(NaiveTime::from_hms(18, 30, 31)));
        } else {
            panic!("wrong date kind");
        }

        let date = Date::new(&[N("/-0031-07%")]).unwrap();
        assert_eq!(date.is_uncertain, true);
        assert_eq!(date.is_approximate, true);
        if let DateValue::Range(DateBound::Open, Definite(end)) = date.value {
            assert_eq!(end.year, -31);
            assert_eq!(end.month, Some(6));
            assert_eq!(end.day, None);
            assert_eq!(end.time, None);
        } else {
            panic!("wrong date kind");
        }
    }

    #[test]
    fn test_new_date_from_three_fields() {
        let year = &[N("2020")];
        let month = &[N("January\u{A0}12th")];
        let date = Date::new_from_three_fields(Some(year), Some(month), None).unwrap();
        if let DateValue::Atom(val) = date.value {
            assert_eq!(val.year, 2020);
            assert_eq!(val.month, Some(0));
            assert_eq!(val.day, Some(11));
            assert_eq!(val.time, None);
        } else {
            panic!("wrong date kind");
        }

        let year = &[N("-0004")];
        let month = &[N("aug")];
        let day = &[N("28")];
        let date =
            Date::new_from_three_fields(Some(year), Some(month), Some(day)).unwrap();
        if let DateValue::Atom(val) = date.value {
            assert_eq!(val.year, -4);
            assert_eq!(val.month, Some(7));
            assert_eq!(val.day, Some(27));
            assert_eq!(val.time, None);
        } else {
            panic!("wrong date kind");
        }
    }
}
