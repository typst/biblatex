use std::cmp::Ordering;
use std::fmt::{self, Display, Formatter};

use chrono::{Datelike, NaiveDate, NaiveTime};
use lazy_static::lazy_static;
use regex::Regex;

use crate::chunk::*;
use crate::Type;

lazy_static! {
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

/// Represents a date or a range of dates and their certainty and exactness.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Date {
    /// The date or the date range.
    pub value: DateValue,
    /// Indicates whether the sources are sure about the date.
    pub is_uncertain: bool,
    /// Indicates the specificity of the date value.
    pub is_approximate: bool,
}

/// Represents a atomic date or a range of dates.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum DateValue {
    /// A single date.
    Atom(Datetime),
    /// A range of dates that may be open or definite at both start and end.
    Range(DateBound, DateBound),
}

/// Indicates whether the start or end of a date interval is open or definite.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum DateBound {
    /// The start or end of the range is open / unknown.
    Open,
    /// The start or end of the range is definite / known.
    Definite(Datetime),
}

/// A timezone-unaware date that must specify a year and may specify month, day,
/// and time. Flags about uncertainity / precision are stored within the parent
/// `Date` struct.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Datetime {
    /// The year.
    ///
    /// AD years are counted starting from one and thus represented as exactly
    /// their year (e.g. 2000 AD is `2000`) whereas BC years are counted
    /// starting from zero downwards (e.g. 1000 BC is `999`)
    pub year: i32,
    /// The month (starting at zero).
    pub month: Option<u8>,
    /// The day (starting at zero).
    pub day: Option<u8>,
    /// The timezone-unaware time.
    pub time: Option<NaiveTime>,
}

impl Date {
    /// Parse a date from a chunk vector.
    pub fn new(chunks: &[Chunk]) -> Option<Self> {
        let mut date_str = chunks.format_verbatim().trim_end().to_string();

        let last_char = date_str.chars().last()?;
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
                    DateBound::Definite(Datetime::new(s1)?)
                };

                let end = if Self::is_open_range(&s2) {
                    DateBound::Open
                } else {
                    DateBound::Definite(Datetime::new(s2)?)
                };

                DateValue::Range(start, end)
            } else {
                if is_uncertain || is_approximate {
                    date_str.pop();
                }

                DateValue::Atom(Datetime::new(date_str)?)
            }
        };

        Some(Self { is_approximate, is_uncertain, value })
    }

    /// Create a new date from the `year`, `month`, and `day` fields.
    pub fn new_from_three_fields(
        year: &[Chunk],
        month: Option<&[Chunk]>,
        day: Option<&[Chunk]>,
    ) -> Option<Self> {
        let mut year = year.format_verbatim();
        year.retain(|c| !c.is_whitespace());

        let capt = YEAR_REGEX.captures(&year)?;
        let year: i32 = capt.name("y").unwrap().as_str().parse().unwrap();
        let mut date_atom = Datetime { year, month: None, day: None, time: None };

        if let Some(month) = month {
            let month = month.format_verbatim();
            if let Some(day) = day {
                let mut day = day.format_verbatim();
                day.retain(|c| !c.is_whitespace());
                let day: u8 = day.parse().ok()?;
                if day > 31 || day < 1 {
                    return None;
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
                        return None;
                    }
                    date_atom.day = Some(day - 1);
                }
            } else if let Some(capt) = MONTH_PART_REGEX.captures(&month) {
                let name = capt.name("m").unwrap().as_str();
                date_atom.month = get_month_for_name(name)
                    .or_else(|| get_month_for_abbr(name).map(|x| x.1));
            }
        }

        Some(Date::new_from_date_atom(date_atom))
    }

    fn new_from_date_atom(atom: Datetime) -> Self {
        Date {
            is_approximate: false,
            is_uncertain: false,
            value: DateValue::Atom(atom),
        }
    }

    fn is_open_range(s: &str) -> bool {
        let s = s.trim();
        if s.is_empty() || s == ".." { true } else { false }
    }

    fn range_dates(mut source: String) -> Option<(Datetime, Datetime)> {
        source.retain(|c| !c.is_whitespace());

        Some(if let Some(captures) = CENTURY_REGEX.captures(&source) {
            let century: i32 = (captures.name("y").unwrap()).as_str().parse().unwrap();
            (
                Datetime {
                    year: century * 100,
                    month: None,
                    day: None,
                    time: None,
                },
                Datetime {
                    year: century * 100 + 99,
                    month: None,
                    day: None,
                    time: None,
                },
            )
        } else if let Some(captures) = DECADE_REGEX.captures(&source) {
            let decade: i32 = (captures.name("y").unwrap()).as_str().parse().unwrap();
            (
                Datetime {
                    year: decade * 10,
                    month: None,
                    day: None,
                    time: None,
                },
                Datetime {
                    year: decade * 10 + 9,
                    month: None,
                    day: None,
                    time: None,
                },
            )
        } else if let Some(captures) = MONTH_UNSURE_REGEX.captures(&source) {
            let year = (captures.name("y").unwrap()).as_str().parse().unwrap();

            (
                Datetime {
                    year,
                    month: Some(0),
                    day: None,
                    time: None,
                },
                Datetime {
                    year,
                    month: Some(11),
                    day: None,
                    time: None,
                },
            )
        } else if let Some(captures) = DAY_MONTH_UNSURE_REGEX.captures(&source) {
            let year = (captures.name("y").unwrap()).as_str().parse().unwrap();

            (
                Datetime {
                    year,
                    month: Some(0),
                    day: Some(0),
                    time: None,
                },
                Datetime {
                    year,
                    month: Some(11),
                    day: Some(30),
                    time: None,
                },
            )
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

            (
                Datetime {
                    year,
                    month: Some(month - 1),
                    day: Some(0),
                    time: None,
                },
                Datetime {
                    year,
                    month: Some(month - 1),
                    day: Some(days as u8 - 1),
                    time: None,
                },
            )
        } else {
            return None;
        })
    }

    pub(crate) fn to_fieldset(&self) -> Vec<(String, String)> {
        let mut res = vec![];
        match self.value {
            DateValue::Atom(date) => {
                let year = if date.year >= 0 {
                    format!("{:04}", date.year)
                } else {
                    format!("{:05}", date.year)
                };

                res.push(("year".to_string(), year));

                if let Some(month) = date.month {
                    res.push(("month".to_string(), format!("{:02}", month + 1)));

                    if let Some(day) = date.day {
                        res.push(("day".to_string(), format!("{:02}", day + 1)));
                    }
                }
            }

            DateValue::Range(start, end) => {
                let mut open = 0;

                if matches!(start, DateBound::Open) {
                    open += 1;
                }
                if matches!(end, DateBound::Open) {
                    open += 1;
                }

                match open {
                    0 => {}
                    1 => {
                        let date = if let DateBound::Definite(date) = start {
                            date
                        } else if let DateBound::Definite(date) = end {
                            date
                        } else {
                            panic!("One DateBound should be definite")
                        };

                        res = Date::new_from_date_atom(date).to_fieldset();
                    }
                    2 => {
                        let start = if let DateBound::Definite(date) = start {
                            date
                        } else {
                            panic!("Start has to be definite at this point")
                        };

                        let end = if let DateBound::Definite(date) = end {
                            date
                        } else {
                            panic!("End has to be definite at this point")
                        };

                        res = Date::new_from_date_atom(start).to_fieldset();
                        let mut end_fieldset =
                            Date::new_from_date_atom(end).to_fieldset();
                        end_fieldset = end_fieldset
                            .into_iter()
                            .map(|(k, v)| (format!("end{}", k), v))
                            .collect();
                        res.append(&mut end_fieldset);
                    }
                    _ => unreachable!(),
                }
            }
        }

        res
    }
}

impl Type for Date {
    fn from_chunks(chunks: &[Chunk]) -> Option<Self> {
        Date::new(chunks)
    }

    fn to_chunks(&self) -> Chunks {
        let uncertainity_symbol = match (self.is_approximate, self.is_uncertain) {
            (true, true) => "%",
            (true, false) => "~",
            (false, true) => "?",
            (false, false) => "",
        };

        vec![Chunk::Normal(match self.value {
            DateValue::Atom(date) => format!("{}{}", date, uncertainity_symbol),
            DateValue::Range(start, end) => {
                format!("{}/{}{}", start, end, uncertainity_symbol)
            }
        })]
    }
}

impl Display for DateBound {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            DateBound::Open => write!(f, ".."),
            DateBound::Definite(atom) => write!(f, "{}", atom),
        }
    }
}

impl Datetime {
    /// Parse a date atom from a string.
    pub fn new(mut source: String) -> Option<Self> {
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

        Some(if let Ok(ndate) = full_date {
            Datetime {
                year: ndate.year(),
                month: Some(ndate.month0() as u8),
                day: Some(ndate.day0() as u8),
                time,
            }
        } else if let Some(captures) = MONTH_REGEX.captures(&source) {
            Datetime {
                year: (captures.name("y").unwrap()).as_str().parse().unwrap(),
                month: Some(
                    (captures.name("m").unwrap()).as_str().parse::<u8>().unwrap() - 1,
                ),
                day: None,
                time,
            }
        } else if let Some(captures) = YEAR_REGEX.captures(&source) {
            Datetime {
                year: (captures.name("y").unwrap()).as_str().parse().unwrap(),
                month: None,
                day: None,
                time,
            }
        } else {
            return None;
        })
    }
}

impl PartialOrd for Datetime {
    fn partial_cmp(&self, other: &Datetime) -> Option<Ordering> {
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

impl Display for Datetime {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if self.year >= 0 {
            write!(f, "{:04}", self.year)?;
        } else {
            write!(f, "{:05}", self.year)?;
        }

        if let Some(month) = self.month {
            if let Some(day) = self.day {
                write!(f, "-{:02}-{:02}", month + 1, day + 1)?;
            } else {
                write!(f, "-{:02}", month + 1)?;
            }
        }

        Ok(())
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chunk::tests::*;
    use DateBound::Definite;

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
        assert_eq!(date.to_chunks(), vec![N("2017-10-25?")]);

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
        assert_eq!(date.to_chunks(), vec![N("1900/1999~")]);

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
        assert_eq!(date.to_chunks(), vec![N("1948-03-02/1950")]);

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
        assert_eq!(date.to_chunks(), vec![N("2020-04-04/..")]);

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
        assert_eq!(date.to_chunks(), vec![N("../-0031-07%")]);
    }

    #[test]
    fn test_new_date_from_three_fields() {
        let year = &[N("2020")];
        let month = &[N("January\u{A0}12th")];
        let date = Date::new_from_three_fields(year, Some(month), None).unwrap();
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
        let date = Date::new_from_three_fields(year, Some(month), Some(day)).unwrap();
        if let DateValue::Atom(val) = date.value {
            assert_eq!(val.year, -4);
            assert_eq!(val.month, Some(7));
            assert_eq!(val.day, Some(27));
            assert_eq!(val.time, None);
        } else {
            panic!("wrong date kind");
        }
    }

    #[test]
    fn test_new_datetime() {
        let atom1 = Datetime::new("2017-10 -25".to_string()).unwrap();
        assert_eq!(atom1.year, 2017);
        assert_eq!(atom1.month, Some(9));
        assert_eq!(atom1.day, Some(24));
        assert_eq!(atom1.time, None);
        assert_eq!(atom1.to_string(), "2017-10-25");

        let atom2 = Datetime::new("  2019 -- 03 ".to_string()).unwrap();
        assert_eq!(atom2.year, 2019);
        assert_eq!(atom2.month, Some(2));
        assert_eq!(atom2.day, None);
        assert_eq!(atom2.time, None);
        assert_eq!(atom2.to_string(), "2019-03");

        let atom3 = Datetime::new("  -0006".to_string()).unwrap();
        assert_eq!(atom3.year, -6);
        assert_eq!(atom3.month, None);
        assert_eq!(atom3.day, None);
        assert_eq!(atom3.time, None);
        assert_eq!(atom3.to_string(), "-0006");

        let atom4 = Datetime::new("2020-09-06T13:39:00".to_string()).unwrap();
        assert_eq!(atom4.year, 2020);
        assert_eq!(atom4.month, Some(8));
        assert_eq!(atom4.day, Some(5));
        assert_eq!(atom4.time, Some(NaiveTime::from_hms(13, 39, 00)));

        assert!(atom3 < atom4);
        assert!(atom2 > atom1);
    }
}
