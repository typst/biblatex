use std::cmp::Ordering;
use std::fmt::{self, Display, Formatter};

use chrono::{Datelike, NaiveDate, NaiveTime};

use crate::chunk::*;
use crate::scanner::Scanner;
use crate::{FieldType, Spanned, Type, TypeError};

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
    pub fn parse(chunks: &[Spanned<Chunk>]) -> Result<Self, FieldType> {
        let date = chunks.format_verbatim().to_uppercase();
        let mut date_trimmed = date.trim_end();

        let (is_uncertain, is_approximate) =
            match &date_trimmed[date_trimmed.len() - 1 ..] {
                "?" => (true, false),
                "~" => (false, true),
                "%" => (true, true),
                _ => (false, false),
            };

        if is_uncertain || is_approximate {
            date_trimmed = &date_trimmed[.. date_trimmed.len() - 1];
        }

        let value = if date_trimmed.contains('X') {
            let (d1, d2) = Self::range_dates(date_trimmed).map_err(|e| e.kind)?;
            DateValue::Between(d1, d2)
        } else {
            if let Some(pos) = date_trimmed.find('/') {
                let s1 = &date_trimmed[.. pos];
                let s2 = &date_trimmed[pos + 1 ..];

                fn is_open_range(s: &str) -> bool {
                    s.trim().is_empty() || s == ".."
                }

                match (is_open_range(&s1), is_open_range(&s2)) {
                    (false, false) => {
                        DateValue::Between(Datetime::parse(s1)?, Datetime::parse(s2)?)
                    }
                    (false, true) => DateValue::After(Datetime::parse(s1)?),
                    (true, false) => DateValue::Before(Datetime::parse(s2)?),
                    (true, true) => return Err(FieldType::Date),
                }
            } else {
                DateValue::At(Datetime::parse(date_trimmed)?)
            }
        };

        Ok(Self {
            approximate: is_approximate,
            uncertain: is_uncertain,
            value,
        })
    }

    /// Create a new date from `year`, `month`, and `day` chunks.
    pub fn parse_three_fields(
        year: &[Spanned<Chunk>],
        month: Option<&[Spanned<Chunk>]>,
        day: Option<&[Spanned<Chunk>]>,
    ) -> Result<Self, TypeError> {
        let year = get_year(&mut Scanner::new(&year.format_verbatim()))
            .map_err(|k| TypeError::new(0 .. 0, k))?;
        let mut date_atom = Datetime { year, month: None, day: None, time: None };

        if let Some(month) = month {
            let month = month.format_verbatim();
            let mut s = Scanner::new(&month);
            s.skip_ws();
            let month = s.eat_while(|c| c.is_ascii_alphabetic());

            date_atom.month = get_month_for_name(month)
                .or_else(|| get_month_for_abbr(month).map(|x| x.1));

            if let Some(day) = day {
                let day = day.format_verbatim();

                let day: u8 = day
                    .trim()
                    .parse()
                    .map_err(|_| TypeError::new(0 .. 0, FieldType::Date))?;
                if day > 31 || day < 1 {
                    return Err(TypeError::new(0 .. 0, FieldType::Date));
                }

                date_atom.day = Some(day - 1);
            } else {
                // Try to read the day from the month field.
                if s.eat_while(|c| c.is_whitespace() || matches!(c, '-' | '\u{00a0}'))
                    .len()
                    == 0
                {
                    return Ok(Date::from_datetime(date_atom));
                };

                let day = s.eat_while(|c| c.is_ascii_digit());
                if day.len() == 0 {
                    return Err(TypeError::new(0 .. 0, FieldType::Date));
                }

                let day: u8 = day.parse().unwrap();

                if day < 1 || day > 31 {
                    return Err(TypeError::new(0 .. 0, FieldType::Date));
                }

                date_atom.day = Some(day - 1);
            }
        }

        Ok(Date::from_datetime(date_atom))
    }

    fn from_datetime(atom: Datetime) -> Self {
        Date {
            approximate: false,
            uncertain: false,
            value: DateValue::At(atom),
        }
    }

    fn range_dates(source: &str) -> Result<(Datetime, Datetime), TypeError> {
        let mut s = Scanner::new(source);
        s.skip_ws();

        let year_part = s.eat_while(|c| c.is_ascii_digit());
        let sure_digits = year_part.len();
        let mut variable = 10_i32.pow(4 - sure_digits as u32);

        if sure_digits < 2 || s.eat_while(|c| c == 'X').len() + sure_digits != 4 {
            return Err(TypeError::new(0 .. s.index(), FieldType::Date));
        }

        let year = year_part.parse::<i32>().unwrap() * variable;
        variable -= 1;

        if sure_digits != 4 {
            return Ok((
                Datetime { year, month: None, day: None, time: None },
                Datetime {
                    year: year + variable,
                    month: None,
                    day: None,
                    time: None,
                },
            ));
        }

        get_hyphen(&mut s)?;

        let idx = s.index();
        match s.eat_while(|c| c == 'X').len() {
            0 => {}
            2 => {
                s.skip_ws();
                if !s.eof() {
                    get_hyphen(&mut s)?;
                    if s.eat_while(|c| c == 'X').len() != 2 {
                        return Err(TypeError::new(s.here(), FieldType::Date));
                    }
                }

                return Ok((
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
                ));
            }
            _ => {
                return Err(TypeError::new(idx .. s.index(), FieldType::Date));
            }
        }

        let month = s.eat_while(|c| c.is_ascii_digit());
        if month.len() != 2 {
            return Err(TypeError::new(idx .. s.index(), FieldType::Date));
        }
        let month: Option<u8> = month.parse().ok();

        get_hyphen(&mut s)?;

        if s.eat_while(|c| c == 'X').len() == 2 {
            s.skip_ws();
            if !s.eof() {
                return Err(TypeError::new(s.here(), FieldType::Date));
            }

            return Ok((
                Datetime { year, month, day: Some(0), time: None },
                Datetime { year, month, day: Some(30), time: None },
            ));
        }

        Err(TypeError::new(s.here(), FieldType::Date))
    }

    pub(crate) fn to_fieldset(&self) -> Vec<(String, String)> {
        self.value.to_fieldset()
    }
}

fn get_year(s: &mut Scanner) -> Result<i32, FieldType> {
    s.skip_ws();
    let year_idx = s.index();
    s.eat_if('-');
    s.skip_ws();

    if s.eat_while(|c| c.is_ascii_digit()).len() != 4 {
        return Err(FieldType::Date);
    }

    Ok(i32::from_str_radix(s.eaten_from(year_idx), 10).unwrap())
}

fn get_hyphen(s: &mut Scanner) -> Result<(), TypeError> {
    s.skip_ws();
    if s.eat_while(|c| c == '-').is_empty() {
        return Err(TypeError::new(s.here(), FieldType::Date));
    }
    s.skip_ws();
    Ok(())
}

impl Type for Date {
    fn from_chunks(chunks: &[Spanned<Chunk>]) -> Result<Self, FieldType> {
        Date::parse(chunks)
    }

    fn to_chunks(&self, start: usize) -> Chunks {
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

        let span = start .. start + s.len();

        vec![Spanned::new(Chunk::Normal(s), span)]
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
    fn parse(mut src: &str) -> Result<Self, FieldType> {
        let time = if let Some(pos) = src.find('T') {
            if pos + 1 < src.len() {
                let time_str = &src[pos + 1 ..];
                src = &src[.. pos];
                time_str.parse::<NaiveTime>().ok()
            } else {
                None
            }
        } else {
            None
        };

        let full_date = src.parse::<NaiveDate>();

        Ok(if let Ok(ndate) = full_date {
            Datetime {
                year: ndate.year(),
                month: Some(ndate.month0() as u8),
                day: Some(ndate.day0() as u8),
                time,
            }
        } else {
            // This might be an incomplete date, missing day and possibly month.
            let mut s = Scanner::new(&src);
            s.skip_ws();
            let year = get_year(&mut s)?;
            s.skip_ws();

            let month = if s.eat_while(|c| c == '-').len() > 0 {
                s.skip_ws();
                let month = s.eat_while(|c| c.is_ascii_digit());
                if month.len() != 2 {
                    return Err(FieldType::Date);
                }

                Some(u8::from_str_radix(&month, 10).unwrap() - 1)
            } else {
                None
            };

            Datetime { year, month, day: None, time: None }
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
pub(crate) fn get_month_for_abbr(month: &str) -> Option<(&'static str, u8)> {
    match month.to_lowercase().as_str() {
        "jan" => Some(("January", 0)),
        "feb" => Some(("February", 1)),
        "mar" => Some(("March", 2)),
        "apr" => Some(("April", 3)),
        "may" => Some(("May", 4)),
        "jun" => Some(("June", 5)),
        "jul" => Some(("July", 6)),
        "aug" => Some(("August", 7)),
        "sep" => Some(("September", 8)),
        "oct" => Some(("October", 9)),
        "nov" => Some(("November", 10)),
        "dec" => Some(("December", 11)),
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
        let date = Date::parse(&[s(N("2017-10 -25?"), 0 .. 12)]).unwrap();
        assert_eq!(date.to_chunks(0), vec![s(N("2017-10-25?"), 0 .. 11)]);
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

        let date = Date::parse(&[s(N("19XX~"), 0 .. 5)]).unwrap();
        assert_eq!(date.to_chunks(0), vec![s(N("1900/1999~"), 0 .. 10)]);
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

        let date = Date::parse(&[s(N("1948-03-02/1950"), 1 .. 16)]).unwrap();
        assert_eq!(date.to_chunks(1), vec![s(N("1948-03-02/1950"), 1 .. 16)]);
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

        let date = Date::parse(&[s(N("2020-04-04T18:30:31/"), 0 .. 20)]).unwrap();
        assert_eq!(date.to_chunks(0), vec![s(N("2020-04-04/.."), 0 .. 13)]);
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

        let date = Date::parse(&[s(N("/-0031-07%"), 0 .. 10)]).unwrap();
        assert_eq!(date.to_chunks(0), vec![s(N("../-0031-07%"), 0 .. 12)]);
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
        let year = &[s(N("2020"), 0 .. 4)];
        let month = &[s(N("January\u{A0}12th"), 20 .. 32)];
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

        let year = &[s(N("-0004"), 0 .. 5)];
        let month = &[s(N("aug"), 41 .. 44)];
        let day = &[s(N("28"), 48 .. 50)];
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
        let date1 = Datetime::parse("2017-10 -25").unwrap();
        assert_eq!(date1.to_string(), "2017-10-25");
        assert_eq!(date1, Datetime {
            year: 2017,
            month: Some(9),
            day: Some(24),
            time: None,
        });

        let date2 = Datetime::parse("  2019 -- 03 ").unwrap();
        assert_eq!(date2, Datetime {
            year: 2019,
            month: Some(2),
            day: None,
            time: None,
        });
        assert_eq!(date2.to_string(), "2019-03");

        let date3 = Datetime::parse("  -0006").unwrap();
        assert_eq!(date3.to_string(), "-0006");
        assert_eq!(date3, Datetime {
            year: -6,
            month: None,
            day: None,
            time: None,
        });

        let date4 = Datetime::parse("2020-09-06T13:39:00").unwrap();
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
