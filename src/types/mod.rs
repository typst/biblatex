//! A collection of strong field types parsable from chunks.

mod date;
mod person;

pub use date::*;
pub use person::*;

use std::ops::Range;
use std::str::FromStr;

use lazy_static::lazy_static;
use numerals::roman::Roman;
use regex::Regex;
use strum::{AsRefStr, Display, EnumString};

use super::*;

/// Convert Bib(La)TeX data types from and to chunk slices.
pub trait Type: Sized {
    /// Parse the type from chunks.
    fn from_chunks(chunks: &[Chunk]) -> Option<Self>;

    /// Serialize the type into chunks.
    fn to_chunks(&self) -> Chunks;
}

impl Type for Vec<Chunks> {
    /// Splits the chunks at `"and"`s.
    fn from_chunks(chunks: &[Chunk]) -> Option<Self> {
        Some(split_token_lists(chunks, "and"))
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
    fn from_chunks(chunks: &[Chunk]) -> Option<Self> {
        Some(
            split_token_lists(chunks, ",")
                .into_iter()
                .map(|chunks| chunks.format_verbatim())
                .collect::<Vec<String>>(),
        )
    }

    fn to_chunks(&self) -> Chunks {
        let chunks: Vec<_> = self.iter().map(|s| Chunk::Normal(s.clone())).collect();
        join_chunk_list(&chunks, ",")
    }
}

impl Type for String {
    fn from_chunks(chunks: &[Chunk]) -> Option<Self> {
        Some(chunks.format_verbatim())
    }

    fn to_chunks(&self) -> Chunks {
        vec![Chunk::Verbatim(self.clone())]
    }
}

impl Type for i64 {
    fn from_chunks(chunks: &[Chunk]) -> Option<Self> {
        let s = chunks.format_verbatim();
        let s = s.trim();

        if let Ok(n) = s.parse::<i64>() {
            Some(n)
        } else if let Some(roman) = Roman::parse(s) {
            Some(roman.value() as i64)
        } else {
            None
        }
    }

    fn to_chunks(&self) -> Chunks {
        vec![Chunk::Normal(self.to_string())]
    }
}

impl Type for Range<u32> {
    fn from_chunks(chunks: &[Chunk]) -> Option<Self> {
        chunks.parse::<Vec<Range<u32>>>()?.into_iter().next()
    }

    fn to_chunks(&self) -> Chunks {
        vec![Chunk::Normal(format!("{}-{}", self.start, self.end))]
    }
}

impl Type for Vec<Range<u32>> {
    fn from_chunks(chunks: &[Chunk]) -> Option<Self> {
        lazy_static! {
            // Range regex (like `5 -- 7`).
            static ref REGEX: Regex = Regex::new(r"(?P<s>\d+)\s*-+\s*(\d+:)?(?P<e>\d+)").unwrap();
        }

        let range_vecs = split_token_lists(chunks, ",");

        let mut res = vec![];
        for range_candidate in range_vecs.iter().map(|f| f.format_verbatim()) {
            let caps = REGEX.captures(&range_candidate);
            if let Some(caps) = caps {
                let start: u32 = caps.name("s").unwrap().as_str().parse().unwrap();
                let end: u32 = caps.name("e").unwrap().as_str().parse().unwrap();
                res.push(start .. end);
            }
        }

        Some(res)
    }

    fn to_chunks(&self) -> Chunks {
        let chunks = self
            .iter()
            .map(|range| Chunk::Normal(format!("{}-{}", range.start, range.end)))
            .collect::<Chunks>();

        join_chunk_list(&chunks, ",")
    }
}

/// An integer or a chunk vector.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum IntOrChunks {
    Int(i64),
    Chunks(Chunks),
}

impl Type for IntOrChunks {
    fn from_chunks(chunks: &[Chunk]) -> Option<Self> {
        Some(if let Some(int) = chunks.parse() {
            IntOrChunks::Int(int)
        } else {
            IntOrChunks::Chunks(chunks.to_vec())
        })
    }

    fn to_chunks(&self) -> Chunks {
        match self {
            IntOrChunks::Int(int) => vec![Chunk::Normal(int.to_string())],
            IntOrChunks::Chunks(chunks) => chunks.clone(),
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
    fn from_chunks(chunks: &[Chunk]) -> Option<Self> {
        Pagination::from_str(&chunks.format_verbatim().to_lowercase()).ok()
    }

    fn to_chunks(&self) -> Chunks {
        vec![Chunk::Normal(self.to_string())]
    }
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

impl Type for EditorType {
    fn from_chunks(chunks: &[Chunk]) -> Option<Self> {
        EditorType::from_str(&chunks.format_verbatim().to_lowercase()).ok()
    }

    fn to_chunks(&self) -> Chunks {
        vec![Chunk::Normal(self.to_string())]
    }
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

impl FromStr for Gender {
    type Err = &'static str;

    /// Two-letter gender serialization in accordance with the BibLaTeX standard.
    fn from_str(s: &str) -> Result<Gender, Self::Err> {
        match s {
            "sf" => Ok(Gender::SingularFemale),
            "sm" => Ok(Gender::SingularMale),
            "sn" => Ok(Gender::SingularNeuter),
            "pf" => Ok(Gender::PluralFemale),
            "pm" => Ok(Gender::PluralMale),
            "pn" => Ok(Gender::PluralNeuter),
            _ => Err("unknown gender identifier"),
        }
    }
}

impl Type for Gender {
    fn from_chunks(chunks: &[Chunk]) -> Option<Self> {
        Gender::from_str(&chunks.format_verbatim().to_lowercase()).ok()
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
