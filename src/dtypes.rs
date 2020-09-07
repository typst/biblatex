extern crate chinese_number;
extern crate chrono;
extern crate inflector;
extern crate numerals;

use crate::parse::Chunk;
use chinese_number::{ChineseNumberCountMethod, ChineseNumberToNumber};
use chrono::prelude::*;
use inflector::Inflector;
use numerals::roman::Roman;
use strum_macros::{EnumString, AsRefStr, Display};
use regex::Regex;

use std::cmp::Ordering;
use std::str::FromStr;

lazy_static! {
    static ref RANGE_REGEX: Regex =
        Regex::new(r"(?P<s>\d+)\s*-+\s*(\d+:)?(?P<e>\d+)").unwrap();

    // Definite date Regexes
    static ref MONTH_REGEX: Regex =
        Regex::new(r"^(?P<y>(\+|-)?\d{4})-+(?P<m>\d{2})").unwrap();
    static ref YEAR_REGEX: Regex = Regex::new(r"^(?P<y>(\+|-)?\d{4})").unwrap();

    // Date range Regexes
    static ref CENTURY_REGEX: Regex = Regex::new(r"^(?P<y>(\+|-)?\d{2})XX").unwrap();
    static ref DECADE_REGEX: Regex = Regex::new(r"^(?P<y>(\+|-)?\d{3})X").unwrap();
    static ref MONTH_UNSURE_REGEX: Regex =
        Regex::new(r"^(?P<y>(\+|-)?\d{4})-+XX").unwrap();
    static ref DAY_UNSURE_REGEX: Regex =
        Regex::new(r"^(?P<y>(\+|-)?\d{4})-*(?P<m>\d{2})-*XX").unwrap();
    static ref DAY_MONTH_UNSURE_REGEX: Regex =
        Regex::new(r"^(?P<y>(\+|-)?\d{4})-*XX-*XX").unwrap();
}

/*********************************
 ********* Name Parsing **********
 *********************************/

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
            let last_space = formatted.rfind(' ').unwrap_or(0);
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
            } else if has_seen_uppercase_words || index >= last_word_start {
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

/*********************************
 ********* Date Parsing **********
 *********************************/

/// A date atom is a timezone-unaware Date that must specify a year
/// and can specify month, day, and time. Flags about uncertainity / precision
/// are stored within the parent `Date` struct.
#[derive(Clone, Debug, PartialEq)]
pub struct DateAtom {
    pub year: i32,
    /// The month (starts at zero).
    pub month: Option<u8>,
    /// The day (starts at zero).
    pub day: Option<u8>,
    pub time: Option<NaiveTime>,
}

impl PartialOrd for DateAtom {
    fn partial_cmp(&self, other: &DateAtom) -> Option<Ordering> {
        let year_ord = self.year.cmp(&other.year);
        if year_ord != Ordering::Equal {
            return Some(year_ord);
        }

        if let Some(month) = self.month {
            if let Some(month_o) = other.month {
                let month_ord = month.cmp(&month_o);
                if month_ord != Ordering::Equal {
                    return Some(month_ord);
                }
            } else {
                return None;
            }
        } else {
            return if other.month.is_none() {
                Some(Ordering::Equal)
            } else {
                None
            };
        }

        if let Some(day) = self.day {
            if let Some(day_o) = other.day {
                let day_ord = day.cmp(&day_o);
                if day_ord != Ordering::Equal {
                    return Some(day_ord);
                }
            } else {
                return None;
            }
        } else {
            return if other.day.is_none() {
                Some(Ordering::Equal)
            } else {
                None
            };
        }

        if let Some(time) = self.time {
            if let Some(time_o) = other.time {
                Some(time.cmp(&time_o))
            } else {
                None
            }
        } else if other.time.is_none() {
            Some(Ordering::Equal)
        } else {
            None
        }
    }
}

impl DateAtom {
    fn new(mut source: String) -> Result<Self, anyhow::Error> {
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

/// Indicates whether the start or end of a date interval is open or definite
#[derive(Clone, Debug, PartialEq)]
pub enum DateKind {
    Open,
    Definite(DateAtom),
}

/// Represents a date or a range of dates.
#[derive(Clone, Debug, PartialEq)]
pub struct Date {
    /// Indicates whether the sources are sure about the date.
    pub is_uncertain: bool,
    /// Indicates the specificity of the date value.
    pub is_approximate: bool,
    /// The date's value, or its start point if `range_end.is_some()`.
    pub value: DateKind,
    /// If this is Some, the date is a range (`Date.value .. Date.range_end`).
    pub range_end: Option<DateKind>,
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

impl Date {
    fn new(chunks: Vec<Chunk>) -> Result<Self, anyhow::Error> {
        let mut date_str = format_verbatim(&chunks).trim_end().to_string();

        let last_char = date_str.chars().last().ok_or(anyhow!("Date string is empty"))?;
        let (is_uncertain, is_approximate) = match last_char {
            '?' => (true, false),
            '~' => (false, true),
            '%' => (true, true),
            _ => (false, false),
        };

        let date;

        let range_end = if date_str.to_uppercase().contains('X') {
            let (d1, d2) = Date::range_dates(date_str)?;
            date = DateKind::Definite(d1);
            Some(DateKind::Definite(d2))
        } else {
            if date_str.contains('/') {
                let (s1, s2) = split_at_normal_char(chunks, '/', true);
                let (s1, mut s2) = (format_verbatim(&s1), format_verbatim(&s2));

                if is_uncertain || is_approximate {
                    s2.pop();
                }

                if Date::is_open_range(&s1) {
                    date = DateKind::Open;
                } else {
                    date = DateKind::Definite(DateAtom::new(s1)?);
                }

                if Date::is_open_range(&s2) {
                    Some(DateKind::Open)
                } else {
                    Some(DateKind::Definite(DateAtom::new(s2)?))
                }
            } else {
                if is_uncertain || is_approximate {
                    date_str.pop();
                }

                date = DateKind::Definite(DateAtom::new(date_str)?);
                None
            }
        };

        Ok(Date {
            is_approximate,
            is_uncertain,
            value: date,
            range_end,
        })
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

    fn range_dates(mut source: String) -> Result<(DateAtom, DateAtom), anyhow::Error> {
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

/*********************************
 ** Chunk type parsing adaptors **
 *********************************/

 /// Implementors represent the serialized form of an Bib(La)TeX data type.
pub trait Type: Sized {
    /// This function allows to extract data out of an
    /// resolved Chunk vector for consumption elsewhere.
    fn parse(chunks: Vec<Chunk>) -> Result<Self, anyhow::Error>;
}

impl Type for Vec<Vec<Chunk>> {
    fn parse(chunks: Vec<Chunk>) -> Result<Self, anyhow::Error> {
        Ok(split_token_lists(chunks, "and"))
    }
}

impl Type for Vec<Person> {
    fn parse(chunks: Vec<Chunk>) -> Result<Self, anyhow::Error> {
        let list = <Vec<Vec<Chunk>>>::parse(chunks)?;
        let mut persons = vec![];

        for pers in list {
            persons.push(Person::new(pers));
        }

        Ok(persons)
    }
}

impl Type for Date {
    fn parse(chunks: Vec<Chunk>) -> Result<Self, anyhow::Error> {
        Date::new(chunks)
    }
}

impl Type for String {
    fn parse(chunks: Vec<Chunk>) -> Result<Self, anyhow::Error> {
        Ok(format_verbatim(&chunks))
    }
}

impl Type for i64 {
    fn parse(chunks: Vec<Chunk>) -> Result<Self, anyhow::Error> {
        parse_integers(&chunks)
    }
}

impl Type for IntOrChunks {
    fn parse(chunks: Vec<Chunk>) -> Result<Self, anyhow::Error> {
        let res = parse_integers(&chunks).ok();
        if res.is_some() {
            Ok(IntOrChunks { int: res, chunks: None })
        } else {
            Ok(IntOrChunks { int: res, chunks: Some(chunks) })
        }
    }
}

impl Type for std::ops::Range<u32> {
    fn parse(chunks: Vec<Chunk>) -> Result<Self, anyhow::Error> {
        let mut ranges = parse_ranges(chunks);

        if !ranges.is_empty() {
            Ok(ranges.remove(0))
        } else {
            Err(anyhow!("No range specified"))
        }
    }
}

impl Type for Vec<std::ops::Range<u32>> {
    fn parse(chunks: Vec<Chunk>) -> Result<Self, anyhow::Error> {
        Ok(parse_ranges(chunks))
    }
}

impl Type for Pagination {
    fn parse(chunks: Vec<Chunk>) -> Result<Self, anyhow::Error> {
        Ok(Pagination::from_str(&format_verbatim(&chunks).to_lowercase())?)
    }
}

impl Type for EditorType {
    fn parse(chunks: Vec<Chunk>) -> Result<Self, anyhow::Error> {
        Ok(EditorType::from_str(&format_verbatim(&chunks).to_lowercase())?)
    }
}

impl Type for Gender {
    fn parse(chunks: Vec<Chunk>) -> Result<Self, anyhow::Error> {
        Gender::from_str(&format_verbatim(&chunks).to_lowercase())
    }
}

/*********************************
 ************ Ranges *************
 *********************************/

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

/*********************************
 *********** Integers ************
 *********************************/

/// Parse integers. This method will accept arabic, roman, and chinese numerals.
fn parse_integers(source: &[Chunk]) -> Result<i64, anyhow::Error> {
    let s = format_verbatim(source);
    let s_t = s.trim();

    if let Ok(n) = str::parse::<i64>(s_t) {
        Ok(n)
    } else if let Some(roman) = Roman::parse(s_t) {
        Ok(roman.value() as i64)
    } else if let Ok(n) = s_t.parse_chinese_number(ChineseNumberCountMethod::TenThousand)
    {
        Ok(n)
    } else {
        Err(anyhow!("Could not parse integer"))
    }
}

pub struct IntOrChunks {
    pub chunks: Option<Vec<Chunk>>,
    pub int: Option<i64>,
}

/*********************************
 ********* Various Enums *********
 *********************************/

#[derive(EnumString, AsRefStr, Display, Debug, Clone, PartialEq)]
#[strum(serialize_all = "snake_case")]
/// How the page increment is triggered.
pub enum Pagination {
    Page,
    Column,
    Line,
    Verse,
    Section,
    Parapgraph,
}

#[derive(EnumString, AsRefStr, Display, Debug, Clone, PartialEq)]
#[strum(serialize_all = "snake_case")]
/// Which role the according editor had (cf. EditorA, EditorB, EditorC fields).
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

#[derive(AsRefStr, Display, Debug, Clone, PartialEq)]
/// Gender of the author or editor (if no author specified).
pub enum Gender {
    SingularFemale,
    SingularMale,
    SingularNeuter,
    PluralFemale,
    PluralMale,
    PluralNeuter,
}

impl std::str::FromStr for Gender {
    type Err = anyhow::Error;

    /// Two-letter gender serialization in accordance with the BibLaTeX standard.
    fn from_str(s: &str) -> ::std::result::Result<Gender, Self::Err> {
        match s {
            "sf" => Ok(Gender::SingularFemale),
            "sm" => Ok(Gender::SingularMale),
            "sn" => Ok(Gender::SingularNeuter),
            "pf" => Ok(Gender::PluralFemale),
            "pm" => Ok(Gender::PluralMale),
            "pn" => Ok(Gender::PluralNeuter),
            _    => Err(anyhow!("Unknown gender identifier")),
        }
    }
}

impl Gender {
    /// Puts the gender into plural.
    pub fn pluralize(&self) -> Self {
        match self {
            Gender::SingularFemale => Gender::PluralFemale,
            Gender::SingularMale => Gender::PluralMale,
            Gender::SingularNeuter => Gender::PluralNeuter,
            _ => self.clone(),
        }
    }

    /// Puts the gender into the singular.
    pub fn singularize(&self) -> Self {
        match self {
            Gender::PluralFemale => Gender::SingularFemale,
            Gender::PluralMale => Gender::SingularMale,
            Gender::PluralNeuter => Gender::SingularNeuter,
            _ => self.clone(),
        }
    }

    /// Finds a gender to summarize a list of genders.
    pub fn coalesce(list: &[Self]) -> Option<Self> {
        if list.is_empty() {
            return None;
        }

        if list.len() == 1 {
            return Some(list[0].clone())
        }

        let mut was_female = false;
        let mut was_male = false;
        let mut was_neuter = false;

        for g in list {
            match g {
                Gender::SingularFemale => { was_female = true; }
                Gender::SingularMale => { was_male = true; }
                Gender::SingularNeuter => { was_neuter = true; }
                Gender::PluralFemale => { was_female = true; }
                Gender::PluralMale => { was_male = true; }
                Gender::PluralNeuter => { was_neuter = true; }
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

/*********************************
 *********** Utilities ***********
 *********************************/

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
    use super::{
        parse_ranges, split_at_normal_char, split_values, Date, DateAtom, DateKind,
        Person, ValueCharIter,
    };
    use crate::parse::Chunk;
    use chrono::NaiveTime;

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

    #[test]
    fn new_date_atom() {
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
    fn new_date() {
        let date = Date::new(vec![N("2017-10 -25?")]).unwrap();
        if let DateKind::Definite(val) = date.value {
            assert_eq!(val.year, 2017);
            assert_eq!(val.month, Some(9));
            assert_eq!(val.day, Some(24));
            assert_eq!(val.time, None);
        } else {
            panic!("Wrong DateKind");
        }
        assert_eq!(date.is_uncertain, true);
        assert_eq!(date.is_approximate, false);
        assert_eq!(date.range_end, None);

        let date = Date::new(vec![N("19XX~")]).unwrap();
        if let DateKind::Definite(val) = date.value {
            assert_eq!(val.year, 1900);
            assert_eq!(val.month, None);
            assert_eq!(val.day, None);
            assert_eq!(val.time, None);
        } else {
            panic!("Wrong DateKind");
        }
        if let DateKind::Definite(val) = date.range_end.unwrap() {
            assert_eq!(val.year, 1999);
            assert_eq!(val.month, None);
            assert_eq!(val.day, None);
            assert_eq!(val.time, None);
        } else {
            panic!("Wrong DateKind");
        }
        assert_eq!(date.is_uncertain, false);
        assert_eq!(date.is_approximate, true);

        let date = Date::new(vec![N("1948-03-02/1950")]).unwrap();
        if let DateKind::Definite(val) = date.value {
            assert_eq!(val.year, 1948);
            assert_eq!(val.month, Some(2));
            assert_eq!(val.day, Some(1));
            assert_eq!(val.time, None);
        } else {
            panic!("Wrong DateKind");
        }
        if let DateKind::Definite(val) = date.range_end.unwrap() {
            assert_eq!(val.year, 1950);
            assert_eq!(val.month, None);
            assert_eq!(val.day, None);
            assert_eq!(val.time, None);
        } else {
            panic!("Wrong DateKind");
        }

        assert_eq!(date.is_uncertain, false);
        assert_eq!(date.is_approximate, false);

        let date = Date::new(vec![N("2020-04-04T18:30:31/")]).unwrap();
        if let DateKind::Definite(val) = date.value {
            assert_eq!(val.year, 2020);
            assert_eq!(val.month, Some(3));
            assert_eq!(val.day, Some(3));
            assert_eq!(val.time, Some(NaiveTime::from_hms(18, 30, 31)));
        } else {
            panic!("Wrong DateKind");
        }
        assert_eq!(date.range_end.unwrap(), DateKind::Open);

        assert_eq!(date.is_uncertain, false);
        assert_eq!(date.is_approximate, false);

        let date = Date::new(vec![N("/-0031-07%")]).unwrap();
        if let DateKind::Definite(val) = date.range_end.unwrap() {
            assert_eq!(val.year, -31);
            assert_eq!(val.month, Some(6));
            assert_eq!(val.day, None);
            assert_eq!(val.time, None);
        } else {
            panic!("Wrong DateKind");
        }
        assert_eq!(date.value, DateKind::Open);

        assert_eq!(date.is_uncertain, true);
        assert_eq!(date.is_approximate, true);
    }
}
