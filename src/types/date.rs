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

/// A date or a range of dates and their certainty and exactness.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Date {
    /// The date or the date range.
    pub value: DateValue,
    /// Indicates whether the sources are sure about the date.
    pub uncertain: bool,
    /// Indicates the specificity of the date value.
    pub approximate: bool,
}

/// A single date or a range of dates.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum DateValue {
    /// A single date.
    At(Datetime),
    /// A range of dates with known start, but open end.
    After(Datetime),
    /// A range of dates with open start, but known end.
    Before(Datetime),
    /// A range of dates with known start and end.
    Between(Datetime, Datetime),
}

/// Timezone-unaware date and time.
///
/// Must specify a year and may specify month, day, and time.
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
    /// Parse a date from chunks.
    pub fn parse(chunks: &[Chunk]) -> Option<Self> {
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
            DateValue::Between(d1, d2)
        } else {
            if date_str.contains('/') {
                let (s1, s2) = split_at_normal_char(chunks, '/', true);
                let (s1, mut s2) = (s1.format_verbatim(), s2.format_verbatim());
                if is_uncertain || is_approximate {
                    s2.pop();
                }

                fn is_open_range(s: &str) -> bool {
                    s.trim().is_empty() || s == ".."
                }

                match (is_open_range(&s1), is_open_range(&s2)) {
                    (false, false) => {
                        DateValue::Between(Datetime::parse(s1)?, Datetime::parse(s2)?)
                    }
                    (false, true) => DateValue::After(Datetime::parse(s1)?),
                    (true, false) => DateValue::Before(Datetime::parse(s2)?),
                    (true, true) => return None,
                }
            } else {
                if is_uncertain || is_approximate {
                    date_str.pop();
                }

                DateValue::At(Datetime::parse(date_str)?)
            }
        };

        Some(Self {
            approximate: is_approximate,
            uncertain: is_uncertain,
            value,
        })
    }

    /// Create a new date from `year`, `month`, and `day` chunks.
    pub fn parse_three_fields(
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

        Some(Date::from_datetime(date_atom))
    }

    fn from_datetime(atom: Datetime) -> Self {
        Date {
            approximate: false,
            uncertain: false,
            value: DateValue::At(atom),
        }
    }

    fn range_dates(mut source: String) -> Option<(Datetime, Datetime)> {
        source.retain(|c| !c.is_whitespace());

        Some(if let Some(captures) = CENTURY_REGEX.captures(&source) {
            let century: i32 = captures.name("y").unwrap().as_str().parse().unwrap();
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
            let decade: i32 = captures.name("y").unwrap().as_str().parse().unwrap();
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
            let year = captures.name("y").unwrap().as_str().parse().unwrap();

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
            let year = captures.name("y").unwrap().as_str().parse().unwrap();
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
            let year = captures.name("y").unwrap().as_str().parse().unwrap();
            let month = captures.name("m").unwrap().as_str().parse::<u8>().unwrap();

            let date = if month == 12 {
                NaiveDate::from_ymd(year + 1, 1, 1)
            } else {
                NaiveDate::from_ymd(year, month as u32 + 1, 1)
            };

            let days = date
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
        self.value.to_fieldset()
    }
}

impl Type for Date {
    fn from_chunks(chunks: &[Chunk]) -> Option<Self> {
        Date::parse(chunks)
    }

    fn to_chunks(&self) -> Chunks {
        let mut s = match self.value {
            DateValue::At(date) => format!("{}", date),
            DateValue::After(start) => format!("{}/..", start),
            DateValue::Before(end) => format!("../{}", end),
            DateValue::Between(start, end) => format!("{}/{}", start, end),
        };

        s.push_str(match (self.approximate, self.uncertain) {
            (true, true) => "%",
            (true, false) => "~",
            (false, true) => "?",
            (false, false) => "",
        });

        vec![Chunk::Normal(s)]
    }
}

impl DateValue {
    pub(crate) fn to_fieldset(&self) -> Vec<(String, String)> {
        match self {
            DateValue::At(date) | DateValue::After(date) | DateValue::Before(date) => {
                date.to_fieldset()
            }

            DateValue::Between(start, end) => {
                let mut set = start.to_fieldset();
                set.extend(
                    end.to_fieldset().into_iter().map(|(k, v)| (format!("end{}", k), v)),
                );
                set
            }
        }
    }
}

impl Datetime {
    /// Parse a datetime from a string.
    fn parse(mut src: String) -> Option<Self> {
        src.retain(|f| !f.is_whitespace());

        let time = if let Some(pos) = src.find('T') {
            if pos + 1 < src.len() {
                let time_str = src.split_off(pos + 1);
                src.pop();
                time_str.parse::<NaiveTime>().ok()
            } else {
                None
            }
        } else {
            None
        };

        let full_date = src.parse::<NaiveDate>();

        Some(if let Ok(ndate) = full_date {
            Datetime {
                year: ndate.year(),
                month: Some(ndate.month0() as u8),
                day: Some(ndate.day0() as u8),
                time,
            }
        } else if let Some(captures) = MONTH_REGEX.captures(&src) {
            Datetime {
                year: (captures.name("y").unwrap()).as_str().parse().unwrap(),
                month: Some(
                    (captures.name("m").unwrap()).as_str().parse::<u8>().unwrap() - 1,
                ),
                day: None,
                time,
            }
        } else if let Some(captures) = YEAR_REGEX.captures(&src) {
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

    pub(crate) fn to_fieldset(&self) -> Vec<(String, String)> {
        let year = if self.year >= 0 {
            format!("{:04}", self.year)
        } else {
            format!("{:05}", self.year)
        };

        let mut fields = vec![("year".to_string(), year)];
        if let Some(month) = self.month {
            fields.push(("month".to_string(), format!("{:02}", month + 1)));

            if let Some(day) = self.day {
                fields.push(("day".to_string(), format!("{:02}", day + 1)));
            }
        }

        fields
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

    #[test]
    fn test_parse_date() {
        let date = Date::parse(&[N("2017-10 -25?")]).unwrap();
        assert_eq!(date.to_chunks(), vec![N("2017-10-25?")]);
        assert_eq!(date, Date {
            value: DateValue::At(Datetime {
                year: 2017,
                month: Some(9),
                day: Some(24),
                time: None,
            }),
            uncertain: true,
            approximate: false,
        });

        let date = Date::parse(&[N("19XX~")]).unwrap();
        assert_eq!(date.to_chunks(), vec![N("1900/1999~")]);
        assert_eq!(date, Date {
            value: DateValue::Between(
                Datetime {
                    year: 1900,
                    month: None,
                    day: None,
                    time: None,
                },
                Datetime {
                    year: 1999,
                    month: None,
                    day: None,
                    time: None,
                }
            ),
            uncertain: false,
            approximate: true,
        });

        let date = Date::parse(&[N("1948-03-02/1950")]).unwrap();
        assert_eq!(date.to_chunks(), vec![N("1948-03-02/1950")]);
        assert_eq!(date, Date {
            value: DateValue::Between(
                Datetime {
                    year: 1948,
                    month: Some(2),
                    day: Some(1),
                    time: None,
                },
                Datetime {
                    year: 1950,
                    month: None,
                    day: None,
                    time: None,
                }
            ),
            uncertain: false,
            approximate: false,
        });

        let date = Date::parse(&[N("2020-04-04T18:30:31/")]).unwrap();
        assert_eq!(date.to_chunks(), vec![N("2020-04-04/..")]);
        assert_eq!(date, Date {
            value: DateValue::After(Datetime {
                year: 2020,
                month: Some(3),
                day: Some(3),
                time: Some(NaiveTime::from_hms(18, 30, 31)),
            }),
            uncertain: false,
            approximate: false,
        });

        let date = Date::parse(&[N("/-0031-07%")]).unwrap();
        assert_eq!(date.to_chunks(), vec![N("../-0031-07%")]);
        assert_eq!(date, Date {
            value: DateValue::Before(Datetime {
                year: -31,
                month: Some(6),
                day: None,
                time: None,
            }),
            uncertain: true,
            approximate: true,
        });
    }

    #[test]
    fn test_parse_date_from_three_fields() {
        let year = &[N("2020")];
        let month = &[N("January\u{A0}12th")];
        let date = Date::parse_three_fields(year, Some(month), None).unwrap();
        assert_eq!(
            date.value,
            DateValue::At(Datetime {
                year: 2020,
                month: Some(0),
                day: Some(11),
                time: None,
            })
        );

        let year = &[N("-0004")];
        let month = &[N("aug")];
        let day = &[N("28")];
        let date = Date::parse_three_fields(year, Some(month), Some(day)).unwrap();
        assert_eq!(
            date.value,
            DateValue::At(Datetime {
                year: -4,
                month: Some(7),
                day: Some(27),
                time: None,
            })
        );
    }

    #[test]
    fn test_parse_datetime() {
        let date1 = Datetime::parse("2017-10 -25".to_string()).unwrap();
        assert_eq!(date1.to_string(), "2017-10-25");
        assert_eq!(date1, Datetime {
            year: 2017,
            month: Some(9),
            day: Some(24),
            time: None,
        });

        let date2 = Datetime::parse("  2019 -- 03 ".to_string()).unwrap();
        assert_eq!(date2.to_string(), "2019-03");
        assert_eq!(date2, Datetime {
            year: 2019,
            month: Some(2),
            day: None,
            time: None,
        });

        let date3 = Datetime::parse("  -0006".to_string()).unwrap();
        assert_eq!(date3.to_string(), "-0006");
        assert_eq!(date3, Datetime {
            year: -6,
            month: None,
            day: None,
            time: None,
        });

        let date4 = Datetime::parse("2020-09-06T13:39:00".to_string()).unwrap();
        assert_eq!(date4, Datetime {
            year: 2020,
            month: Some(8),
            day: Some(5),
            time: Some(NaiveTime::from_hms(13, 39, 00)),
        });

        assert!(date3 < date4);
        assert!(date2 > date1);
    }
}
