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

use crate::raw::ParseError;
use crate::scanner::Scanner;
use crate::{chunk::*, Span};

#[derive(Debug, Clone)]
pub struct MalformedError {
    span: Span,
    kind: MalformKind,
}

impl MalformedError {
    pub(crate) fn new(span: Span, kind: MalformKind) -> Self {
        Self { span, kind }
    }
}

impl fmt::Display for MalformedError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "malformed {}: {}-{}",
            self.kind, self.span.start, self.span.end
        )
    }
}

#[derive(Debug, Display, Copy, Clone)]
#[strum(serialize_all = "snake_case")]
pub enum MalformKind {
    Date,
    Gender,
    Integer,
    IntegerRange,
    Pagination,
    EditorType,
}

/// Convert Bib(La)TeX data types from and to chunk slices.
pub trait Type: Sized {
    /// Parse the type from chunks.
    fn from_chunks(chunks: &[Chunk]) -> Result<Self, MalformKind>;

    /// Serialize the type into chunks.
    fn to_chunks(&self) -> Chunks;
}

impl Type for i64 {
    fn from_chunks(chunks: &[Chunk]) -> Result<Self, MalformKind> {
        let s = chunks.format_verbatim();
        let s = s.trim();

        if let Ok(n) = s.parse::<i64>() {
            Ok(n)
        } else if let Some(roman) = Roman::parse(s) {
            Ok(roman.value() as i64)
        } else {
            Err(MalformKind::Integer)
        }
    }

    fn to_chunks(&self) -> Chunks {
        vec![Chunk::Normal(self.to_string())]
    }
}

impl Type for String {
    fn from_chunks(chunks: &[Chunk]) -> Result<Self, MalformKind> {
        Ok(chunks.format_verbatim())
    }

    fn to_chunks(&self) -> Chunks {
        vec![Chunk::Verbatim(self.clone())]
    }
}

impl Type for Range<u32> {
    fn from_chunks(chunks: &[Chunk]) -> Result<Self, MalformKind> {
        chunks
            .parse::<Vec<Range<u32>>>()
            .map_err(|e| e.kind)?
            .into_iter()
            .next()
            .ok_or(MalformKind::IntegerRange)
    }

    fn to_chunks(&self) -> Chunks {
        vec![Chunk::Normal(format!("{}-{}", self.start, self.end))]
    }
}

impl Type for Vec<Chunks> {
    /// Splits the chunks at `"and"`s.
    fn from_chunks(chunks: &[Chunk]) -> Result<Self, MalformKind> {
        Ok(split_token_lists(chunks, " and "))
    }

    fn to_chunks(&self) -> Chunks {
        let mut merged = vec![];

        let mut chunks = self.iter();
        if let Some(chunk) = chunks.next() {
            merged.extend(chunk.iter().cloned());

            for chunk in chunks {
                merged.push(Chunk::Normal(" and ".to_string()));
                merged.extend(chunk.iter().cloned());
            }
        }

        merged
    }
}

impl Type for Vec<String> {
    /// Splits the chunks at commas.
    fn from_chunks(chunks: &[Chunk]) -> Result<Self, MalformKind> {
        Ok(split_token_lists(chunks, ",")
            .into_iter()
            .map(|chunks| chunks.format_verbatim())
            .collect::<Vec<String>>())
    }

    fn to_chunks(&self) -> Chunks {
        let chunks: Vec<_> = self.iter().map(|s| Chunk::Normal(s.clone())).collect();
        join_chunk_list(&chunks, ",")
    }
}

impl Type for Vec<Range<u32>> {
    /// Splits the ranges at commas.
    fn from_chunks(chunks: &[Chunk]) -> Result<Self, MalformKind> {
        let range_vecs = split_token_lists(chunks, ",");
        let mut res = vec![];

        let number = |s: &mut Scanner| -> Result<u32, MalformKind> {
            s.skip_ws();
            let num = s.eat_while(|c| c.is_digit(10));
            u32::from_str(num).map_err(|_| MalformKind::IntegerRange)
        };

        let component = |s: &mut Scanner| -> Result<u32, MalformKind> {
            loop {
                let num = number(s)?;
                s.skip_ws();
                if !s.eat_if(':') {
                    return Ok(num);
                }
            }
        };

        for range_candidate in range_vecs.iter().map(|f| f.format_verbatim()) {
            let mut s = Scanner::new(&range_candidate);
            let start = component(&mut s)?;
            s.skip_ws();
            if !s.eat_if('-') {
                res.push(start .. start);
                continue;
            }
            s.eat_while(|c| c == '-');
            s.skip_ws();
            let end = component(&mut s)?;
            res.push(start .. end);
        }

        Ok(res)
    }

    fn to_chunks(&self) -> Chunks {
        let chunks = self
            .iter()
            .map(|range| Chunk::Normal(format!("{}-{}", range.start, range.end)))
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
    fn from_chunks(chunks: &[Chunk]) -> Result<Self, MalformKind> {
        Ok(if let Ok(int) = chunks.parse() {
            Edition::Int(int)
        } else {
            Edition::Chunks(chunks.to_vec())
        })
    }

    fn to_chunks(&self) -> Chunks {
        match self {
            Edition::Int(int) => vec![Chunk::Normal(int.to_string())],
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
    fn from_chunks(chunks: &[Chunk]) -> Result<Self, MalformKind> {
        Pagination::from_str(&chunks.format_verbatim().to_lowercase())
            .map_err(|_| MalformKind::Pagination)
    }

    fn to_chunks(&self) -> Chunks {
        vec![Chunk::Normal(self.to_string())]
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
    fn from_chunks(chunks: &[Chunk]) -> Result<Self, MalformKind> {
        EditorType::from_str(&chunks.format_verbatim().to_lowercase())
            .map_err(|_| MalformKind::EditorType)
    }

    fn to_chunks(&self) -> Chunks {
        vec![Chunk::Normal(self.to_string())]
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
    fn from_chunks(chunks: &[Chunk]) -> Result<Self, MalformKind> {
        // Two-letter gender serialization in accordance with the BibLaTeX standard.
        match chunks.format_verbatim().to_lowercase().as_ref() {
            "sf" => Ok(Gender::SingularFemale),
            "sm" => Ok(Gender::SingularMale),
            "sn" => Ok(Gender::SingularNeuter),
            "pf" => Ok(Gender::PluralFemale),
            "pm" => Ok(Gender::PluralMale),
            "pn" => Ok(Gender::PluralNeuter),
            _ => Err(MalformKind::Gender),
        }
    }

    fn to_chunks(&self) -> Chunks {
        vec![Chunk::Normal(self.to_string())]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chunk::tests::*;

    #[test]
    fn test_ranges() {
        let ranges = &[N("31--43,21:4-21:6,  194 --- 245")];
        let res = ranges.parse::<Vec<Range<u32>>>().unwrap();
        assert_eq!(res[0], 31 .. 43);
        assert_eq!(res[1], 4 .. 6);
        assert_eq!(res[2], 194 .. 245);
    }
}
