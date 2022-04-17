//! A collection of strong field types parsable from chunks.

mod date;
mod person;

pub use date::*;
pub use person::*;

use std::fmt;
use std::ops::Range;
use std::str::FromStr;

use numerals::roman::Roman;
use strum::{AsRefStr, Display, EnumString};

use crate::{chunk::*, Span, Spanned};
use unscanny::Scanner;

/// An error that may occur while parsing the chunks in a field into a specific
/// [`Type`].
#[derive(Debug, Clone, PartialEq)]
pub struct TypeError {
    /// Where in the source the error occurred.
    pub span: Span,
    /// What kind of error occurred.
    pub kind: TypeErrorKind,
}

impl TypeError {
    pub(crate) fn new(span: Span, kind: TypeErrorKind) -> Self {
        Self { span, kind }
    }

    fn offset(&mut self, amount: usize) {
        self.span.start += amount;
        self.span.end += amount;
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}-{}", self.kind, self.span.start, self.span.end)
    }
}

/// Error conditions that might occur while parsing the chunks in a field into a specific
/// [`Type`].
///
/// Also see [`TypeError`].
#[derive(Debug, Clone, PartialEq)]
pub enum TypeErrorKind {
    /// The date range was open on both sides.
    UndefinedRange,
    /// The day in a date was out of range (1-31).
    DayOutOfRange,
    /// The month in a date was out of range (1-12).
    MonthOutOfRange,
    /// The given input did not contain a valid number.
    InvalidNumber,
    /// A number did not have the right number of digits.
    WrongNumberOfDigits,
    /// The entry was not in a format valid for that type.
    InvalidFormat,
    /// There is no [`Gender`] variant for this input.
    UnknownGender,
    /// There was no integer range.
    InvalidIntegerRange,
    /// There is no [`Pagination`] variant for this input.
    UnknownPagination,
    /// There is no [`EditorType`] variant for this input.
    UnknownEditorType,
}

impl fmt::Display for TypeErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
            Self::UndefinedRange => "range must not be open on both sides",
            Self::DayOutOfRange => "day out of range (must be between 1 and 31)",
            Self::MonthOutOfRange => "month out of range (must be between 1 and 12)",
            Self::InvalidNumber => "invalid number",
            Self::WrongNumberOfDigits => "wrong number of digits",
            Self::InvalidFormat => "invalid format",
            Self::UnknownGender => "unknown gender",
            Self::InvalidIntegerRange => "invalid integer range",
            Self::UnknownPagination => "unknown pagination",
            Self::UnknownEditorType => "unknown editor type",
        })
    }
}

/// Convert Bib(La)TeX data types from and to chunk slices.
pub trait Type: Sized {
    /// Parse the type from chunks.
    fn from_chunks(chunks: &[Spanned<Chunk>]) -> Result<Self, TypeError>;

    /// Serialize the type into chunks.
    fn to_chunks(&self, start: usize) -> Chunks;
}

impl Type for i64 {
    fn from_chunks(chunks: &[Spanned<Chunk>]) -> Result<Self, TypeError> {
        let span = chunks.span();
        let s = chunks.format_verbatim();
        let s = s.trim();

        if let Ok(n) = s.parse::<i64>() {
            Ok(n)
        } else if let Some(roman) = Roman::parse(s) {
            Ok(roman.value() as i64)
        } else {
            Err(TypeError::new(span, TypeErrorKind::InvalidNumber))
        }
    }

    fn to_chunks(&self, start: usize) -> Chunks {
        let str = self.to_string();
        let span = start .. start + str.len();
        vec![Spanned::new(Chunk::Normal(str), span)]
    }
}

impl Type for String {
    fn from_chunks(chunks: &[Spanned<Chunk>]) -> Result<Self, TypeError> {
        Ok(chunks.format_verbatim())
    }

    fn to_chunks(&self, start: usize) -> Chunks {
        vec![Spanned::new(
            Chunk::Verbatim(self.clone()),
            start .. start + self.len(),
        )]
    }
}

impl Type for Range<u32> {
    fn from_chunks(chunks: &[Spanned<Chunk>]) -> Result<Self, TypeError> {
        let span = chunks.span();
        chunks
            .parse::<Vec<Range<u32>>>()?
            .into_iter()
            .next()
            .ok_or(TypeError::new(span, TypeErrorKind::InvalidIntegerRange))
    }

    fn to_chunks(&self, start: usize) -> Chunks {
        let str = format!("{}-{}", self.start, self.end);
        let span = start .. start + str.len();
        vec![Spanned::new(Chunk::Normal(str), span)]
    }
}

impl Type for Vec<Chunks> {
    /// Splits the chunks at `"and"`s.
    fn from_chunks(chunks: &[Spanned<Chunk>]) -> Result<Self, TypeError> {
        Ok(split_token_lists(chunks, " and "))
    }

    fn to_chunks(&self, start: usize) -> Chunks {
        let mut merged = vec![];
        let mut first = true;

        for chunk in self {
            if first {
                first = false;
            } else {
                merged.push(Spanned::new(
                    Chunk::Normal(" and ".to_string()),
                    if let Some(chunk) = chunk.first() {
                        chunk.span.start .. chunk.span.start
                    } else {
                        start .. start
                    },
                ));
            }

            merged.extend(chunk.clone());
        }

        merged
    }
}

impl Type for Vec<String> {
    /// Splits the chunks at commas.
    fn from_chunks(chunks: &[Spanned<Chunk>]) -> Result<Self, TypeError> {
        Ok(split_token_lists(chunks, ",")
            .into_iter()
            .map(|chunks| chunks.format_verbatim())
            .collect::<Vec<String>>())
    }

    fn to_chunks(&self, start: usize) -> Chunks {
        let mut len = 0;
        let chunks: Vec<_> = self
            .iter()
            .map(|s| {
                let res = Spanned::new(
                    Chunk::Normal(s.clone()),
                    start + len .. start + len + s.len(),
                );
                len += s.len();
                res
            })
            .collect();
        join_chunk_list(&chunks, ",")
    }
}

impl Type for Vec<Range<u32>> {
    /// Splits the ranges at commas.
    fn from_chunks(chunks: &[Spanned<Chunk>]) -> Result<Self, TypeError> {
        let range_vecs = split_token_lists(chunks, ",");
        let mut res = vec![];

        let number = |s: &mut Scanner, offset: usize| -> Result<u32, TypeError> {
            s.eat_whitespace();
            let idx = s.cursor();
            let num = s.eat_while(|c: char| c.is_digit(10));
            u32::from_str(num).map_err(|_| {
                TypeError::new(
                    idx + offset .. s.cursor() + offset,
                    TypeErrorKind::InvalidNumber,
                )
            })
        };

        let component = |s: &mut Scanner, offset: usize| -> Result<u32, TypeError> {
            loop {
                let num = number(s, offset)?;
                s.eat_whitespace();
                if !s.eat_if(':') {
                    return Ok(num);
                }
            }
        };

        for (range_candidate, span) in
            range_vecs.iter().map(|f| (f.format_verbatim(), f.span()))
        {
            let mut s = Scanner::new(&range_candidate);
            let start = component(&mut s, span.start)?;
            s.eat_whitespace();
            if !s.eat_if('-') {
                res.push(start .. start);
                continue;
            }
            s.eat_while('-');
            s.eat_whitespace();
            let end = component(&mut s, span.start)?;
            res.push(start .. end);
        }

        Ok(res)
    }

    fn to_chunks(&self, start: usize) -> Chunks {
        let mut len = 0;

        let chunks = self
            .iter()
            .map(|range| {
                let str = format!("{}-{}", range.start, range.end);
                let span = start + len .. start + len + str.len();
                len += str.len();
                Spanned::new(Chunk::Normal(str), span)
            })
            .collect::<Chunks>();

        join_chunk_list(&chunks, ",")
    }
}

/// The edition of a printed publication.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Edition {
    /// An integer edition.
    Int(i64),
    /// A literal edition, for example `"Reprinted, and revised edition"`.
    Chunks(Chunks),
}

impl Type for Edition {
    fn from_chunks(chunks: &[Spanned<Chunk>]) -> Result<Self, TypeError> {
        Ok(if let Ok(int) = chunks.parse() {
            Edition::Int(int)
        } else {
            Edition::Chunks(chunks.to_vec())
        })
    }

    fn to_chunks(&self, start: usize) -> Chunks {
        match self {
            Edition::Int(int) => {
                let res = int.to_string();
                let span = start .. start + res.len();
                vec![Spanned::new(Chunk::Normal(res), span)]
            }
            Edition::Chunks(chunks) => chunks.clone(),
        }
    }
}

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

impl Type for Pagination {
    fn from_chunks(chunks: &[Spanned<Chunk>]) -> Result<Self, TypeError> {
        let span = chunks.span();
        Pagination::from_str(&chunks.format_verbatim().to_lowercase())
            .map_err(|_| TypeError::new(span, TypeErrorKind::UnknownPagination))
    }

    fn to_chunks(&self, start: usize) -> Chunks {
        let res = self.to_string();
        let span = start .. start + res.len();
        vec![Spanned::new(Chunk::Normal(res), span)]
    }
}

/// Which role the according editor had.
///
/// The value of the `editor` through `editorc` fields.
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

impl Type for EditorType {
    fn from_chunks(chunks: &[Spanned<Chunk>]) -> Result<Self, TypeError> {
        let span = chunks.span();
        EditorType::from_str(&chunks.format_verbatim().to_lowercase())
            .map_err(|_| TypeError::new(span, TypeErrorKind::UnknownEditorType))
    }

    fn to_chunks(&self, start: usize) -> Chunks {
        let res = self.to_string();
        let span = start .. start + res.len();
        vec![Spanned::new(Chunk::Normal(res), span)]
    }
}

/// Gender of the author or editor (if no author was specified).
#[derive(Debug, Copy, Clone, Eq, PartialEq, Display, AsRefStr)]
pub enum Gender {
    SingularFemale,
    SingularMale,
    SingularNeuter,
    PluralFemale,
    PluralMale,
    PluralNeuter,
}

impl Gender {
    /// Puts the gender into plural.
    pub fn plural(self) -> Self {
        match self {
            Gender::SingularFemale => Gender::PluralFemale,
            Gender::SingularMale => Gender::PluralMale,
            Gender::SingularNeuter => Gender::PluralNeuter,
            _ => self,
        }
    }

    /// Puts the gender into the singular.
    pub fn singular(self) -> Self {
        match self {
            Gender::PluralFemale => Gender::SingularFemale,
            Gender::PluralMale => Gender::SingularMale,
            Gender::PluralNeuter => Gender::SingularNeuter,
            _ => self,
        }
    }

    /// Finds a gender that summarizes a list of genders.
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
        } else if was_male && !was_female && !was_neuter {
            Some(Gender::PluralMale)
        } else {
            Some(Gender::PluralNeuter)
        }
    }
}

impl Type for Gender {
    fn from_chunks(chunks: &[Spanned<Chunk>]) -> Result<Self, TypeError> {
        // Two-letter gender serialization in accordance with the BibLaTeX standard.
        let span = chunks.span();
        match chunks.format_verbatim().to_lowercase().as_ref() {
            "sf" => Ok(Gender::SingularFemale),
            "sm" => Ok(Gender::SingularMale),
            "sn" => Ok(Gender::SingularNeuter),
            "pf" => Ok(Gender::PluralFemale),
            "pm" => Ok(Gender::PluralMale),
            "pn" => Ok(Gender::PluralNeuter),
            _ => Err(TypeError::new(span, TypeErrorKind::UnknownGender)),
        }
    }

    fn to_chunks(&self, start: usize) -> Chunks {
        let res = self.to_string();
        let span = start .. start + res.len();
        vec![Spanned::new(Chunk::Normal(res), span)]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chunk::tests::*;

    #[test]
    fn test_ranges() {
        let ranges = &[Spanned::zero(N("31--43,21:4-21:6,  194 --- 245"))];
        let res = ranges.parse::<Vec<Range<u32>>>().unwrap();
        assert_eq!(res[0], 31 .. 43);
        assert_eq!(res[1], 4 .. 6);
        assert_eq!(res[2], 194 .. 245);
    }
}
