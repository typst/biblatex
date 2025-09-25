//! A collection of strong field types parsable from chunks.

mod date;
mod lang;
mod person;

pub use date::*;
pub use lang::*;
pub use person::*;

use std::fmt;
use std::ops::Range;
use std::str::FromStr;

use roman_numerals_rs::RomanNumeral;
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
        self.span.start = self.span.start.saturating_add(amount);
        self.span.end = self.span.end.saturating_add(amount);
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}-{}", self.kind, self.span.start, self.span.end)
    }
}

impl std::error::Error for TypeError {}

/// Error conditions that might occur while parsing the chunks in a field into a specific
/// [`Type`].
///
/// Also see [`TypeError`].
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum TypeErrorKind {
    /// The date range was open on both sides.
    UndefinedRange,
    /// The day in a date was out of range (1-31).
    DayOutOfRange,
    /// The month in a date was out of range (1-12).
    MonthOutOfRange,
    /// The given input did not contain a valid number.
    InvalidNumber,
    /// The given input did not contain a number.
    MissingNumber,
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
    /// There is no [`Language`] variant for this input.
    UnknownLangId,
    /// The year 0 CE or BCE does not exist.
    YearZeroCE,
}

impl fmt::Display for TypeErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
            Self::UndefinedRange => "range must not be open on both sides",
            Self::DayOutOfRange => "day out of range (must be between 1 and 31)",
            Self::MonthOutOfRange => "month out of range (must be between 1 and 12)",
            Self::InvalidNumber => "invalid number",
            Self::MissingNumber => "missing number",
            Self::WrongNumberOfDigits => "wrong number of digits",
            Self::InvalidFormat => "invalid format",
            Self::UnknownGender => "unknown gender",
            Self::InvalidIntegerRange => "invalid integer range",
            Self::UnknownPagination => "unknown pagination",
            Self::UnknownEditorType => "unknown editor type",
            Self::UnknownLangId => "unknown language id",
            Self::YearZeroCE => "year 0 CE or BCE does not exist",
        })
    }
}

/// Convert Bib(La)TeX data types from and to chunk slices.
pub trait Type: Sized {
    /// Parse the type from chunks.
    fn from_chunks(chunks: ChunksRef) -> Result<Self, TypeError>;

    /// Serialize the type into chunks.
    ///
    /// This produces chunks with _detached spans_ that must not be used to
    /// index the source file. Also see [`Spanned`] for more information.
    fn to_chunks(&self) -> Chunks;
}

impl Type for i64 {
    fn from_chunks(chunks: ChunksRef) -> Result<Self, TypeError> {
        let span = chunks.span();
        let s = chunks.format_verbatim();
        let s = s.trim();

        if let Ok(n) = s.parse::<i64>() {
            Ok(n)
        } else if let Ok(roman) = s.parse::<RomanNumeral>() {
            Ok(roman.as_u16() as i64)
        } else if span.is_empty() {
            Err(TypeError::new(span, TypeErrorKind::MissingNumber))
        } else {
            Err(TypeError::new(span, TypeErrorKind::InvalidNumber))
        }
    }

    fn to_chunks(&self) -> Chunks {
        let str = self.to_string();
        vec![Spanned::detached(Chunk::Normal(str))]
    }
}

impl Type for String {
    fn from_chunks(chunks: ChunksRef) -> Result<Self, TypeError> {
        Ok(chunks.format_verbatim())
    }

    fn to_chunks(&self) -> Chunks {
        vec![Spanned::detached(Chunk::Verbatim(self.clone()))]
    }
}

impl Type for Range<u32> {
    fn from_chunks(chunks: ChunksRef) -> Result<Self, TypeError> {
        let span = chunks.span();
        chunks
            .parse::<Vec<Range<u32>>>()?
            .into_iter()
            .next()
            .ok_or(TypeError::new(span, TypeErrorKind::InvalidIntegerRange))
    }

    fn to_chunks(&self) -> Chunks {
        let str = format!("{}-{}", self.start, self.end);
        vec![Spanned::detached(Chunk::Normal(str))]
    }
}

impl Type for Vec<Chunks> {
    /// Splits the chunks at `"and"`s.
    fn from_chunks(chunks: ChunksRef) -> Result<Self, TypeError> {
        Ok(split_token_lists_with_kw(chunks, "and"))
    }

    fn to_chunks(&self) -> Chunks {
        let mut merged = vec![];
        let mut first = true;

        for chunk in self {
            if first {
                first = false;
            } else {
                merged.push(Spanned::detached(Chunk::Normal(" and ".to_string())));
            }

            merged.extend(chunk.clone());
        }

        merged
    }
}

impl Type for Vec<String> {
    /// Splits the chunks at commas.
    fn from_chunks(chunks: ChunksRef) -> Result<Self, TypeError> {
        Ok(split_token_lists(chunks, ",")
            .into_iter()
            .map(|chunks| chunks.format_verbatim())
            .collect::<Vec<String>>())
    }

    fn to_chunks(&self) -> Chunks {
        let chunks: Vec<_> = self
            .iter()
            .map(|s| Spanned::detached(Chunk::Normal(s.clone())))
            .collect();
        join_chunk_list(&chunks, ",")
    }
}

impl Type for Vec<Range<u32>> {
    /// Splits the ranges at commas.
    fn from_chunks(chunks: ChunksRef) -> Result<Self, TypeError> {
        let range_vecs = split_token_lists(chunks, ",");
        let mut res = vec![];

        let number = |s: &mut Scanner, offset: usize| -> Result<u32, TypeError> {
            s.eat_whitespace();
            let idx = s.cursor();
            let num = s.eat_while(|c: char| c.is_ascii_digit());
            u32::from_str(num).map_err(|_| {
                TypeError::new(
                    idx + offset..s.cursor() + offset,
                    TypeErrorKind::InvalidNumber,
                )
            })
        };

        for (range_candidate, span) in
            range_vecs.iter().map(|f| (f.format_verbatim(), f.span()))
        {
            let mut s = Scanner::new(&range_candidate);
            let start = number(&mut s, span.start)?;
            s.eat_whitespace();

            // The double and triple hyphen is converted into en dashes and em
            // dashes earlier.
            if !s.eat_if(['-', '–', '—']) {
                res.push(start..start);
                if !s.done() {
                    return Err(TypeError::new(span, TypeErrorKind::InvalidNumber));
                }
                continue;
            }
            s.eat_while('-');
            s.eat_whitespace();
            let offset = s.cursor();
            let end = number(&mut s, span.start)?;
            if !s.done() {
                return Err(TypeError::new(
                    offset..span.end,
                    TypeErrorKind::InvalidNumber,
                ));
            }
            res.push(start..end);
        }

        Ok(res)
    }

    fn to_chunks(&self) -> Chunks {
        let chunks = self
            .iter()
            .map(|range| {
                let str = format!("{}-{}", range.start, range.end);
                Spanned::detached(Chunk::Normal(str))
            })
            .collect::<Chunks>();

        join_chunk_list(&chunks, ",")
    }
}

/// A value that could be either a typed value or a literal string.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum PermissiveType<T: Type> {
    /// A typed version of the value.
    Typed(T),
    /// A literal string, for example `"Reprinted, and revised edition"`.
    Chunks(Chunks),
}

impl<T> Type for PermissiveType<T>
where
    T: Type,
{
    fn from_chunks(chunks: ChunksRef) -> Result<Self, TypeError> {
        Ok(if let Ok(val) = chunks.parse() {
            PermissiveType::Typed(val)
        } else {
            PermissiveType::Chunks(chunks.to_vec())
        })
    }

    fn to_chunks(&self) -> Chunks {
        match self {
            PermissiveType::Typed(val) => val.to_chunks(),
            PermissiveType::Chunks(chunks) => chunks.clone(),
        }
    }
}

impl Type for Vec<PermissiveType<Language>> {
    /// Splits the chunks at `"and"`s.
    fn from_chunks(chunks: ChunksRef) -> Result<Self, TypeError> {
        split_token_lists_with_kw(chunks, "and")
            .iter()
            .map(|c| PermissiveType::<Language>::from_chunks(c))
            .collect()
    }

    fn to_chunks(&self) -> Chunks {
        let mut merged = vec![];
        let mut first = true;

        for chunk in self {
            if first {
                first = false;
            } else {
                merged.push(Spanned::detached(Chunk::Verbatim(" and ".to_string())));
            }

            merged.extend(chunk.to_chunks());
        }

        merged
    }
}

/// Defines the pagination scheme to use for formatting purposes.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Display, EnumString, AsRefStr)]
#[strum(serialize_all = "snake_case")]
#[allow(missing_docs)]
pub enum Pagination {
    Page,
    Column,
    Line,
    Verse,
    Section,
    Paragraph,
}

impl Type for Pagination {
    fn from_chunks(chunks: ChunksRef) -> Result<Self, TypeError> {
        let span = chunks.span();
        Pagination::from_str(&chunks.format_verbatim().to_lowercase())
            .map_err(|_| TypeError::new(span, TypeErrorKind::UnknownPagination))
    }

    fn to_chunks(&self) -> Chunks {
        let res = self.to_string();
        vec![Spanned::detached(Chunk::Normal(res))]
    }
}

/// Which role the according editor had.
///
/// The value of the `editor` through `editorc` fields.
#[derive(Debug, Clone, Eq, PartialEq, Display, EnumString, AsRefStr)]
#[strum(serialize_all = "snake_case")]
#[allow(missing_docs)]
pub enum EditorType {
    Editor,
    Compiler,
    Founder,
    Continuator,
    Redactor,
    Reviser,
    Collaborator,
    Organizer,
    Director,

    #[strum(default)]
    Unknown(String),
}

impl Type for EditorType {
    fn from_chunks(chunks: ChunksRef) -> Result<Self, TypeError> {
        let span = chunks.span();
        EditorType::from_str(&chunks.format_verbatim().to_lowercase())
            .map_err(|_| TypeError::new(span, TypeErrorKind::UnknownEditorType))
    }

    fn to_chunks(&self) -> Chunks {
        let res = self.to_string();
        vec![Spanned::detached(Chunk::Normal(res))]
    }
}

/// Gender of the author or editor (if no author was specified).
#[derive(Debug, Copy, Clone, Eq, PartialEq, Display, AsRefStr)]
#[allow(missing_docs)]
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
    fn from_chunks(chunks: ChunksRef) -> Result<Self, TypeError> {
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

    fn to_chunks(&self) -> Chunks {
        let res = self.to_string();
        vec![Spanned::detached(Chunk::Normal(res))]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{chunk::tests::*, Bibliography};

    #[test]
    fn test_ranges() {
        let ranges = &[Spanned::zero(N("31--43,4-6,  194 --- 245"))];
        let res = ranges.parse::<Vec<Range<u32>>>().unwrap();
        assert_eq!(res[0], 31..43);
        assert_eq!(res[1], 4..6);
        assert_eq!(res[2], 194..245);
    }

    #[test]
    fn test_ranges_2228() {
        let ranges = &[Spanned::zero(N("34,37--39"))];
        let res = ranges.parse::<Vec<Range<u32>>>().unwrap();
        assert_eq!(res[0], 34..34);
        assert_eq!(res[1], 37..39);
    }

    // Hayagriva issue #340
    #[test]
    fn test_non_numeric_page_ranges() {
        let bib = Bibliography::parse(
            r#"@inproceedings{test,
          author = {John Doe},
          title = {Interesting Findings},
          journal = {Example Journal},
          year = {2024},
          pages = {1A1}
        }"#,
        )
        .unwrap();
        let t = bib.get("test").unwrap();
        let pages = t.get("pages").unwrap();
        let parsed: PermissiveType<std::ops::Range<u32>> = pages.parse().unwrap();
        let PermissiveType::Chunks(chunks) = parsed else {
            panic!("Expected chunks");
        };
        let parsed_chunks: String = chunk_chars(&chunks).map(|(c, _)| c).collect();
        assert_eq!(parsed_chunks, "1A1");
    }

    #[test]
    fn test_non_numeric_page_ranges_2() {
        let bib = Bibliography::parse(
            r#"@inproceedings{test,
            author = {John Doe},
            title = {Interesting Findings},
            journal = {Example Journal},
            year = {2024},
            pages = {hello world! this is a page!}
        }"#,
        )
        .unwrap();
        let t = bib.get("test").unwrap();
        let pages = t.get("pages").unwrap();
        let parsed: PermissiveType<std::ops::Range<u32>> = pages.parse().unwrap();
        let PermissiveType::Chunks(chunks) = parsed else {
            panic!("Expected chunks");
        };
        let parsed_chunks: String = chunk_chars(&chunks).map(|(c, _)| c).collect();
        assert_eq!(parsed_chunks, "hello world! this is a page!");
    }
}
