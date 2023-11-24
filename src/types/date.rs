use std::cmp::Ordering;
use std::fmt::{self, Display, Formatter};
use std::str::FromStr;

use crate::chunk::*;
use crate::{Span, Spanned, Type, TypeError, TypeErrorKind};
use unscanny::Scanner;

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
    /// their year (e.g., 2000 AD is `2000`) whereas BC years are counted
    /// starting from zero downwards (e.g., 1000 BC is `999`)
    pub year: i32,
    /// The month (starting at zero).
    pub month: Option<u8>,
    /// The day (starting at zero).
    pub day: Option<u8>,
    /// The timezone-unaware time.
    pub time: Option<Time>,
}

/// A potentially timezone aware time.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Time {
    /// The hour (0-23).
    pub hour: u8,
    /// The minute (0-59).
    pub minute: u8,
    /// The second (0-59).
    pub second: u8,
    /// An optional timezone offset.
    pub offset: Option<TimeOffset>,
}

impl Time {
    /// Create a new time from hours, minutes, and seconds. Return `None` if
    /// the values are out of range.
    pub fn from_hms(hour: u8, minute: u8, second: u8) -> Option<Self> {
        if hour > 23 || minute > 59 || second > 59 {
            return None;
        }

        Some(Self { hour, minute, second, offset: None })
    }

    /// Create a new time from hours, minutes, seconds and an offset. Return
    /// `None` if the values are out of range.
    pub fn from_hms_offset(
        hour: u8,
        minute: u8,
        second: u8,
        offset: TimeOffset,
    ) -> Option<Self> {
        if hour > 23 || minute > 59 || second > 59 {
            return None;
        }

        Some(Self { hour, minute, second, offset: Some(offset) })
    }

    /// Return seconds in UTC.
    pub fn to_utc_seconds(&self) -> isize {
        let mut seconds =
            self.hour as isize * 3600 + self.minute as isize * 60 + self.second as isize;
        if let Some(offset) = self.offset {
            seconds -= offset.to_seconds();
        }
        seconds
    }
}

impl PartialOrd for Time {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self.offset, other.offset) {
            (Some(_), Some(_)) | (None, None) => {
                Some(self.to_utc_seconds().cmp(&other.to_utc_seconds()))
            }
            _ => None,
        }
    }
}

/// A timezone offset.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TimeOffset {
    /// Time is UTC. Do not assume an origin timezone.
    Utc,
    /// Offset relative to UTC. Positiveness, hour, and minute.
    Offset {
        /// Whether the time is ahead of UTC.
        positive: bool,
        /// The hour offset.
        hours: u8,
        /// The minute offset.
        minutes: u8,
    },
}

impl TimeOffset {
    /// Create a new offset.
    pub fn offset(positive: bool, hours: u8, minutes: u8) -> Self {
        Self::Offset { positive, hours, minutes }
    }

    /// Create a new offset from an hour.
    pub fn offset_hour(hour: i32) -> Self {
        if hour < 0 {
            Self::Offset { positive: false, hours: (-hour) as u8, minutes: 0 }
        } else {
            Self::Offset { positive: true, hours: hour as u8, minutes: 0 }
        }
    }

    /// Convert to seconds.
    fn to_seconds(self) -> isize {
        match self {
            TimeOffset::Utc => 0,
            TimeOffset::Offset { positive, hours, minutes } => {
                let mut seconds = hours as isize * 3600 + minutes as isize * 60;
                if !positive {
                    seconds *= -1;
                }
                seconds
            }
        }
    }
}

impl Date {
    /// Parse a date from chunks.
    pub fn parse(chunks: ChunksRef) -> Result<Self, TypeError> {
        let span = chunks.span();
        let date = chunks.format_verbatim().to_uppercase();

        let mut date_trimmed = date.trim_end();
        let is_both = date_trimmed.ends_with('%');
        let is_uncertain = is_both || date_trimmed.ends_with('?');
        let is_approximate = is_both || date_trimmed.ends_with('~');
        if is_uncertain || is_approximate {
            date_trimmed = &date_trimmed[..date_trimmed.len() - 1];
        }

        let value = if date_trimmed.contains('X') {
            let (d1, d2) = Self::range_dates(date_trimmed).map_err(|mut e| {
                e.offset(span.start);
                e
            })?;
            DateValue::Between(d1, d2)
        } else if let Some(pos) = date_trimmed.find('/') {
            let s1 = &date_trimmed[..pos];
            let s2 = &date_trimmed[pos + 1..];

            fn is_open_range(s: &str) -> bool {
                s.trim().is_empty() || s == ".."
            }

            match (is_open_range(s1), is_open_range(s2)) {
                (false, false) => DateValue::Between(
                    Datetime::parse(s1).map_err(|mut e| {
                        e.offset(span.start);
                        e
                    })?,
                    Datetime::parse(s2).map_err(|mut e| {
                        e.offset(span.start + pos + 1);
                        e
                    })?,
                ),
                (false, true) => {
                    DateValue::After(Datetime::parse(s1).map_err(|mut e| {
                        e.offset(span.start);
                        e
                    })?)
                }
                (true, false) => {
                    DateValue::Before(Datetime::parse(s2).map_err(|mut e| {
                        e.offset(span.start + pos + 1);
                        e
                    })?)
                }
                (true, true) => {
                    return Err(TypeError::new(span, TypeErrorKind::UndefinedRange));
                }
            }
        } else {
            DateValue::At(Datetime::parse(date_trimmed).map_err(|mut e| {
                e.offset(span.start);
                e
            })?)
        };

        Ok(Self {
            approximate: is_approximate,
            uncertain: is_uncertain,
            value,
        })
    }

    /// Create a new date from `year`, `month`, and `day` chunks.
    pub fn parse_three_fields(
        year: ChunksRef,
        month: Option<ChunksRef>,
        day: Option<ChunksRef>,
    ) -> Result<Self, TypeError> {
        let year =
            get_year(&mut Scanner::new(&year.format_verbatim())).map_err(|mut e| {
                e.offset(year.span().start);
                e
            })?;
        let mut date_atom = Datetime { year, month: None, day: None, time: None };

        if let Some(month) = month {
            let month = month.format_verbatim();
            let mut s = Scanner::new(&month);
            s.eat_whitespace();
            let month = s.eat_while(char::is_ascii_alphabetic);

            date_atom.month = get_month_for_name(month)
                .or_else(|| get_month_for_abbr(month).map(|x| x.1));

            if let Some(day) = day {
                let span = day.span();
                let day = day.format_verbatim();

                let day: u8 = day.trim().parse().map_err(|_| {
                    if span.is_empty() {
                        TypeError::new(span.clone(), TypeErrorKind::MissingNumber)
                    } else {
                        TypeError::new(span.clone(), TypeErrorKind::InvalidNumber)
                    }
                })?;
                if !(1..=31).contains(&day) {
                    return Err(TypeError::new(span, TypeErrorKind::DayOutOfRange));
                }

                date_atom.day = Some(day - 1);
            } else {
                // Try to read the day from the month field.
                if s.eat_while(|c: char| {
                    c.is_whitespace() || matches!(c, '-' | '\u{00a0}')
                })
                .is_empty()
                {
                    return Ok(Date::from_datetime(date_atom));
                };

                let day_start = s.cursor();
                let day = s.eat_while(char::is_ascii_digit);
                let day_span = day_start..s.cursor();
                if day.is_empty() {
                    return Err(TypeError::new(day_span, TypeErrorKind::MissingNumber));
                }

                let day: u8 = day.parse().unwrap();

                if !(1..=31).contains(&day) {
                    return Err(TypeError::new(day_span, TypeErrorKind::DayOutOfRange));
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
        s.eat_whitespace();

        let year_part = s.eat_while(char::is_ascii_digit);
        let sure_digits = year_part.len();
        let mut variable = 10_i32.pow(4 - sure_digits as u32);

        if sure_digits < 2 || s.eat_while('X').len() + sure_digits != 4 {
            return Err(TypeError::new(
                0..s.cursor(),
                TypeErrorKind::WrongNumberOfDigits,
            ));
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

        let idx = s.cursor();
        match s.eat_while('X').len() {
            0 => {}
            2 => {
                s.eat_whitespace();
                if !s.done() {
                    get_hyphen(&mut s)?;
                    if s.eat_while('X').len() != 2 {
                        return Err(TypeError::new(
                            here(&s),
                            TypeErrorKind::InvalidFormat,
                        ));
                    }
                }

                return Ok((
                    Datetime { year, month: Some(0), day: None, time: None },
                    Datetime { year, month: Some(11), day: None, time: None },
                ));
            }
            _ => {
                return Err(TypeError::new(
                    idx..s.cursor(),
                    TypeErrorKind::WrongNumberOfDigits,
                ));
            }
        }

        let month_start = s.cursor();
        let month = s.eat_while(char::is_ascii_digit);
        if month.len() != 2 {
            return Err(TypeError::new(
                idx..s.cursor(),
                TypeErrorKind::WrongNumberOfDigits,
            ));
        }
        let month: u8 = month.parse::<u8>().unwrap() - 1;

        if month > 11 {
            return Err(TypeError::new(
                month_start..s.cursor(),
                TypeErrorKind::MonthOutOfRange,
            ));
        }

        get_hyphen(&mut s)?;

        if s.eat_while('X').len() == 2 {
            s.eat_whitespace();
            if !s.done() {
                return Err(TypeError::new(here(&s), TypeErrorKind::InvalidFormat));
            }

            return Ok((
                Datetime { year, month: Some(month), day: Some(0), time: None },
                Datetime {
                    year,
                    month: Some(month),
                    day: Some(30),
                    time: None,
                },
            ));
        }

        Err(TypeError::new(here(&s), TypeErrorKind::InvalidFormat))
    }

    pub(crate) fn to_fieldset(self) -> Vec<(String, String)> {
        self.value.to_fieldset()
    }
}

fn get_year(s: &mut Scanner) -> Result<i32, TypeError> {
    s.eat_whitespace();
    let year_idx = s.cursor();
    let has_sign = s.eat_if(['-', '+']);
    s.eat_whitespace();
    let digits = s.eat_while(char::is_ascii_digit);

    if digits.is_empty() || digits.len() > 4 {
        return Err(TypeError::new(
            year_idx..s.cursor(),
            TypeErrorKind::WrongNumberOfDigits,
        ));
    }

    // This is guaranteed to only contain digits, whitespace, and a sign.
    let year = s.from(year_idx).parse::<i32>().unwrap();

    if let Some(positive_era) = parse_era_marker(s)? {
        if has_sign {
            return Err(TypeError::new(
                year_idx..s.cursor(),
                TypeErrorKind::InvalidFormat,
            ));
        }

        if year == 0 {
            return Err(TypeError::new(year_idx..s.cursor(), TypeErrorKind::YearZeroCE));
        }

        if !positive_era {
            return Ok(-year + 1);
        }
    }

    Ok(year)
}

fn parse_era_marker(s: &mut Scanner) -> Result<Option<bool>, TypeError> {
    s.eat_whitespace();
    let era_idx = s.cursor();
    if s.eat_if("AD") || s.eat_if("CE") {
        if s.peek().map_or(false, |c| c.is_alphanumeric()) {
            return Err(TypeError::new(
                era_idx..s.cursor(),
                TypeErrorKind::InvalidFormat,
            ));
        }

        return Ok(Some(true));
    }

    if s.eat_if("BC") {
        s.eat_if("E");
        if s.peek().map_or(false, |c| c.is_alphanumeric()) {
            return Err(TypeError::new(
                era_idx..s.cursor(),
                TypeErrorKind::InvalidFormat,
            ));
        }

        return Ok(Some(false));
    }

    Ok(None)
}

fn get_hyphen(s: &mut Scanner) -> Result<(), TypeError> {
    s.eat_whitespace();
    if s.eat_while('-').is_empty() {
        return Err(TypeError::new(here(s), TypeErrorKind::InvalidFormat));
    }
    s.eat_whitespace();
    Ok(())
}

fn here(s: &Scanner) -> Span {
    s.cursor()..s.cursor()
}

impl Type for Date {
    fn from_chunks(chunks: ChunksRef) -> Result<Self, TypeError> {
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

        vec![Spanned::detached(Chunk::Normal(s))]
    }
}

impl DateValue {
    pub(crate) fn to_fieldset(self) -> Vec<(String, String)> {
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
    fn parse(src: &str) -> Result<Self, TypeError> {
        let mut s = Scanner::new(src);
        let pos = s.cursor();
        let year = parse_short_year(&mut s).or_else(|_| {
            s.jump(pos);
            parse_year(&mut s)
        })?;

        let mut month = None;
        let mut day = None;

        s.eat_whitespace();

        if s.done() {
            return Ok(Datetime { year, month, day, time: None });
        }

        parse_hyphen(&mut s)?;

        let some_month = parse_month(&mut s)?;
        month = Some(some_month);

        s.eat_whitespace();

        if s.done() {
            return Ok(Datetime { year, month, day, time: None });
        }

        parse_hyphen(&mut s)?;

        let some_day = parse_day(&mut s)?;
        day = Some(some_day);

        if some_day + 1 > days_in_month(some_month, year) {
            return Err(TypeError::new(pos..s.cursor(), TypeErrorKind::DayOutOfRange));
        }

        s.eat_whitespace();
        if s.done() {
            return Ok(Datetime { year, month, day, time: None });
        }

        if !s.eat_if('T') {
            return Err(TypeError::new(pos..s.cursor(), TypeErrorKind::InvalidFormat));
        }

        let hour = parse_hour(&mut s)?;
        s.eat_whitespace();

        if s.done() {
            return Ok(Datetime {
                year,
                month,
                day,
                time: Some(Time { hour, minute: 0, second: 0, offset: None }),
            });
        }

        parse_colon(&mut s)?;
        let minute = parse_minutes_or_seconds(&mut s)?;
        s.eat_whitespace();

        if s.done() {
            return Ok(Datetime {
                year,
                month,
                day,
                time: Some(Time { hour, minute, second: 0, offset: None }),
            });
        }

        parse_colon(&mut s)?;
        let second = parse_minutes_or_seconds(&mut s)?;
        s.eat_whitespace();

        if s.done() {
            return Ok(Datetime {
                year,
                month,
                day,
                time: Some(Time { hour, minute, second, offset: None }),
            });
        }

        let offset = parse_offset(&mut s)?;

        Ok(Datetime {
            year,
            month,
            day,
            time: Some(Time { hour, minute, second, offset: Some(offset) }),
        })
    }

    pub(crate) fn to_fieldset(self) -> Vec<(String, String)> {
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
            (Some(s), Some(o)) => s.partial_cmp(&o),
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

fn parse_int<R>(s: &mut Scanner, digits: R) -> Option<i32>
where
    R: std::ops::RangeBounds<usize>,
{
    s.eat_whitespace();

    let sign = s.eat_if(|c| c == '+' || c == '-');
    let positive = if sign { !s.before().ends_with('-') } else { true };

    s.eat_whitespace();
    let num = s.eat_while(char::is_numeric);
    if !digits.contains(&num.len()) {
        return None;
    }

    let num = num.parse::<i32>().unwrap() * if positive { 1 } else { -1 };
    Some(num)
}

fn parse_unsigned_int<T, R>(s: &mut Scanner, digits: R) -> Option<T>
where
    T: FromStr + Ord + std::fmt::Debug,
    <T as FromStr>::Err: std::fmt::Debug,
    R: std::ops::RangeBounds<usize>,
{
    s.eat_whitespace();
    let num = s.eat_while(char::is_numeric);
    if !digits.contains(&num.len()) {
        return None;
    }

    let num = num.parse::<T>().unwrap();
    Some(num)
}

/// Parse a string with a plus/minus and one to four digits into an integer.
fn parse_year(s: &mut Scanner) -> Result<i32, TypeError> {
    let pos = s.cursor();
    parse_int(s, 4..=4)
        .ok_or_else(|| TypeError::new(pos..s.cursor(), TypeErrorKind::InvalidFormat))
}

fn parse_short_year(s: &mut Scanner) -> Result<i32, TypeError> {
    let pos = s.cursor();
    let year = parse_int(s, 2..=2)
        .ok_or_else(|| TypeError::new(pos..s.cursor(), TypeErrorKind::InvalidFormat))?;
    let year = if year < 50 { year + 2000 } else { year + 1900 };
    Ok(year)
}

/// Parse the month in the 0-11 range.
fn parse_month(s: &mut Scanner) -> Result<u8, TypeError> {
    let pos = s.cursor();
    let month: u8 = parse_unsigned_int(s, 1..=2)
        .ok_or_else(|| TypeError::new(pos..s.cursor(), TypeErrorKind::InvalidFormat))?;
    if !(1..=12).contains(&month) {
        return Err(TypeError::new(pos..s.cursor(), TypeErrorKind::MonthOutOfRange));
    }

    Ok(month - 1)
}

/// Parse the day in the 0-30 range.
fn parse_day(s: &mut Scanner) -> Result<u8, TypeError> {
    let pos = s.cursor();
    let day: u8 = parse_unsigned_int(s, 1..=2)
        .ok_or_else(|| TypeError::new(pos..s.cursor(), TypeErrorKind::InvalidFormat))?;
    if !(1..=31).contains(&day) {
        return Err(TypeError::new(pos..s.cursor(), TypeErrorKind::DayOutOfRange));
    }

    Ok(day - 1)
}

/// Parse the hour in the 0-23 range.
fn parse_hour(s: &mut Scanner) -> Result<u8, TypeError> {
    let pos = s.cursor();
    let hour: u8 = parse_unsigned_int(s, 1..=2)
        .ok_or_else(|| TypeError::new(pos..s.cursor(), TypeErrorKind::InvalidFormat))?;
    if !(0..=23).contains(&hour) {
        return Err(TypeError::new(pos..s.cursor(), TypeErrorKind::InvalidNumber));
    }

    Ok(hour)
}

/// Parse minutes or seconds in the 0-59 range.
fn parse_minutes_or_seconds(s: &mut Scanner) -> Result<u8, TypeError> {
    let pos = s.cursor();
    let num: u8 = parse_unsigned_int(s, 1..=2)
        .ok_or_else(|| TypeError::new(pos..s.cursor(), TypeErrorKind::InvalidFormat))?;
    if !(0..=59).contains(&num) {
        return Err(TypeError::new(pos..s.cursor(), TypeErrorKind::InvalidNumber));
    }

    Ok(num)
}

/// Parse an offset.
fn parse_offset(s: &mut Scanner) -> Result<TimeOffset, TypeError> {
    s.eat_whitespace();
    let pos = s.cursor();
    let c = s.eat();
    Ok(match c {
        Some('Z') => TimeOffset::Utc,
        Some('+' | '-') => {
            let positive = c == Some('+');
            let hours = parse_hour(s)?;
            s.eat_whitespace();
            if s.done() {
                return Ok(TimeOffset::Offset { positive, hours, minutes: 0 });
            }

            parse_colon(s)?;
            let minutes = parse_minutes_or_seconds(s)?;
            TimeOffset::Offset { positive, hours, minutes }
        }
        _ => return Err(TypeError::new(pos..s.cursor(), TypeErrorKind::InvalidFormat)),
    })
}

/// Parse a hyphen.
pub fn parse_hyphen(s: &mut Scanner) -> Result<(), TypeError> {
    let pos = s.cursor();
    s.eat_whitespace();
    if !s.eat_if('-') {
        return Err(TypeError::new(pos..s.cursor(), TypeErrorKind::InvalidFormat));
    }
    s.eat_while('-');
    Ok(())
}

/// Parse a colon.
pub fn parse_colon(s: &mut Scanner) -> Result<(), TypeError> {
    let pos = s.cursor();
    s.eat_whitespace();
    if !s.eat_if(':') {
        return Err(TypeError::new(pos..s.cursor(), TypeErrorKind::InvalidFormat));
    }
    Ok(())
}

fn days_in_month(month: u8, year: i32) -> u8 {
    if month == 1 {
        if year % 4 == 0 && (year % 100 != 0 || year % 400 == 0) {
            29
        } else {
            28
        }
    } else if month < 7 {
        31 - month % 2
    } else {
        30 + month % 2
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
    fn test_parse_empty_date() {
        assert!(Date::parse(&[]).is_err());
        assert!(Date::parse(&[s(N(""), 0..0)]).is_err());
    }

    #[test]
    fn test_parse_date() {
        let date = Date::parse(&[s(N("2017-10 -25?"), 0..12)]).unwrap();
        assert_eq!(date.to_chunks(), vec![d(N("2017-10-25?"))]);
        assert_eq!(
            date,
            Date {
                value: DateValue::At(Datetime {
                    year: 2017,
                    month: Some(9),
                    day: Some(24),
                    time: None,
                }),
                uncertain: true,
                approximate: false,
            }
        );

        let date = Date::parse(&[s(N("19XX~"), 0..5)]).unwrap();
        assert_eq!(date.to_chunks(), vec![d(N("1900/1999~"))]);
        assert_eq!(
            date,
            Date {
                value: DateValue::Between(
                    Datetime { year: 1900, month: None, day: None, time: None },
                    Datetime { year: 1999, month: None, day: None, time: None }
                ),
                uncertain: false,
                approximate: true,
            }
        );

        let date = Date::parse(&[s(N("1948-03-02/1950"), 1..16)]).unwrap();
        assert_eq!(date.to_chunks(), vec![d(N("1948-03-02/1950"))]);
        assert_eq!(
            date,
            Date {
                value: DateValue::Between(
                    Datetime {
                        year: 1948,
                        month: Some(2),
                        day: Some(1),
                        time: None,
                    },
                    Datetime { year: 1950, month: None, day: None, time: None }
                ),
                uncertain: false,
                approximate: false,
            }
        );

        let date = Date::parse(&[s(N("2020-04-04T18:30:31/"), 0..20)]).unwrap();
        assert_eq!(date.to_chunks(), vec![d(N("2020-04-04/.."))]);
        assert_eq!(
            date,
            Date {
                value: DateValue::After(Datetime {
                    year: 2020,
                    month: Some(3),
                    day: Some(3),
                    time: Some(Time::from_hms(18, 30, 31).unwrap()),
                }),
                uncertain: false,
                approximate: false,
            }
        );

        let date = Date::parse(&[s(N("/-0031-07%"), 0..10)]).unwrap();
        assert_eq!(date.to_chunks(), vec![d(N("../-0031-07%"))]);
        assert_eq!(
            date,
            Date {
                value: DateValue::Before(Datetime {
                    year: -31,
                    month: Some(6),
                    day: None,
                    time: None,
                }),
                uncertain: true,
                approximate: true,
            }
        );
    }

    #[test]
    fn test_parse_date_from_three_fields() {
        let year = &[s(N("2020"), 0..4)];
        let month = &[s(N("January\u{A0}12th"), 20..32)];
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

        let year = &[s(N("-0004"), 0..5)];
        let month = &[s(N("aug"), 41..44)];
        let day = &[s(N("28"), 48..50)];
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
    fn test_parse_bce_year() {
        let year = &[s(N("3 AD"), 0..4)];
        let date = Date::parse_three_fields(year, None, None).unwrap();
        assert_eq!(
            date.value,
            DateValue::At(Datetime { year: 3, month: None, day: None, time: None })
        );

        let year = &[s(N("3 BCE"), 0..5)];
        let date = Date::parse_three_fields(year, None, None).unwrap();
        assert_eq!(
            date.value,
            DateValue::At(Datetime { year: -2, month: None, day: None, time: None })
        );

        let year = &[s(N("90"), 0..2)];
        let date = Date::parse_three_fields(year, None, None).unwrap();
        assert_eq!(
            date.value,
            DateValue::At(Datetime { year: 90, month: None, day: None, time: None })
        );
    }

    #[test]
    fn test_parse_datetime() {
        let date1 = Datetime::parse("2017-10 -25").unwrap();
        assert_eq!(date1.to_string(), "2017-10-25");
        assert_eq!(
            date1,
            Datetime {
                year: 2017,
                month: Some(9),
                day: Some(24),
                time: None,
            }
        );

        let date2 = Datetime::parse("  2019 -- 03 ").unwrap();
        assert_eq!(date2, Datetime { year: 2019, month: Some(2), day: None, time: None });
        assert_eq!(date2.to_string(), "2019-03");

        let date3 = Datetime::parse("  -0006").unwrap();
        assert_eq!(date3.to_string(), "-0006");
        assert_eq!(date3, Datetime { year: -6, month: None, day: None, time: None });

        let date4 = Datetime::parse("2020-09-06T13:39:00").unwrap();
        assert_eq!(
            date4,
            Datetime {
                year: 2020,
                month: Some(8),
                day: Some(5),
                time: Some(Time::from_hms(13, 39, 00).unwrap()),
            }
        );

        let date5 = Datetime::parse("2020-09-06T13:39:00Z").unwrap();
        assert_eq!(
            date5,
            Datetime {
                year: 2020,
                month: Some(8),
                day: Some(5),
                time: Some(Time::from_hms_offset(13, 39, 00, TimeOffset::Utc).unwrap()),
            }
        );

        let date6 = Datetime::parse("2020-09-06T13:39:00+01").unwrap();
        assert_eq!(
            date6,
            Datetime {
                year: 2020,
                month: Some(8),
                day: Some(5),
                time: Some(
                    Time::from_hms_offset(13, 39, 00, TimeOffset::offset_hour(1))
                        .unwrap()
                ),
            }
        );

        let date6 = Datetime::parse("2020-09-06T13:39:00-02:10").unwrap();
        assert_eq!(
            date6,
            Datetime {
                year: 2020,
                month: Some(8),
                day: Some(5),
                time: Some(
                    Time::from_hms_offset(13, 39, 00, TimeOffset::offset(false, 2, 10))
                        .unwrap()
                ),
            }
        );

        assert!(date3 < date4);
        assert!(date2 > date1);
    }
}
