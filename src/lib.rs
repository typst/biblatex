pub mod raw;
pub mod types;

mod resolve;

use std::collections::HashMap;

use anyhow::anyhow;

use crate::raw::RawBibliography;
use crate::resolve::resolve;
use crate::types::{Date, IntOrChunks, Person, Type};

/// A fully parsed bibliography.
pub struct Bibliography(pub Vec<Entry>);

/// A bibliography entry that is parsed into chunks, which can be
/// parsed into more specific types on demand on field accesses.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Entry {
    /// The citation key.
    pub cite_key: String,
    /// Denotes the type of bibliography item (e.g. `article`).
    pub entry_type: String,
    /// Maps from field names to their associated chunk vectors.
    pub fields: HashMap<String, Vec<Chunk>>,
}

/// A chunk represents one part of a field value.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Chunk {
    /// Normal values within quotes or single braces subject to
    /// capitalization formatting.
    Normal(String),
    /// Values nested in braces that are to be printed like specified
    /// in the file. Escapes keywords.
    ///
    /// Example: `"Inside {NASA}"` or `{Memes are {gReAT}}`.
    Verbatim(String),
}

impl Bibliography {
    /// Parse a bibliography from a source string.
    pub fn from_str(src: &str, allow_bibtex: bool) -> Vec<Entry> {
        Self::from_raw(RawBibliography::from_str(src, allow_bibtex))
    }

    /// Parse a bibliography from a raw bibliography.
    pub fn from_raw(raw: RawBibliography) -> Vec<Entry> {
        let abbreviations = &raw.abbreviations;
        raw.entries
            .into_iter()
            .map(|entry| Entry {
                cite_key: entry.cite_key.to_string(),
                entry_type: entry.entry_type.to_lowercase().to_string(),
                fields: entry
                    .fields
                    .into_iter()
                    .map(|(key, value)| (key.to_string(), resolve(value, abbreviations)))
                    .collect(),
            })
            .collect()
    }

    /// Try to find an entry with the given cite key.
    pub fn get(&self, cite_key: &str) -> Option<&Entry> {
        self.0.iter().find(|entry| entry.cite_key == cite_key)
    }

    /// An iterator over the bibliography's entries.
    pub fn iter<'a>(&'a self) -> std::slice::Iter<'a, Entry> {
        self.0.iter()
    }
}

impl IntoIterator for Bibliography {
    type Item = Entry;
    type IntoIter = std::vec::IntoIter<Entry>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl Entry {
    /// Get the chunk slice for a field.
    pub fn get(&self, key: &str) -> Option<&[Chunk]> {
        self.fields.get(&key.to_lowercase()).map(AsRef::as_ref)
    }

    /// Get the chunk slice for a field and parse it as a specific type.
    pub fn get_as<T: Type>(&self, key: &str) -> anyhow::Result<T> {
        self.get(key)
            .ok_or_else(|| anyhow!("The {} field is not present", key))
            .and_then(|chunks| chunks.parse::<T>())
    }
}

macro_rules! fields {
    ($($getter:ident: $field_name:expr $(=> $res:ty)?),* $(,)*) => {
        $(
            #[doc = "Get and parse the `"]
            #[doc = $field_name]
            #[doc = "` field."]
            pub fn $getter(&self) -> anyhow::Result<fields!(@type $($res)?)> {
                self.get($field_name)
                    .ok_or_else(|| anyhow!("The {} field is not present", $field_name))
                    $(.and_then(|chunks| chunks.parse::<$res>()))?
            }
        )*
    };

    (@type) => {&[Chunk]};
    (@type $res:ty) => {$res};
}

impl Entry {
    /// Get and parse the `date` field, falling back to the `year`, `month` and `day`
    /// fields when not present.
    pub fn get_date(&self) -> anyhow::Result<Date> {
        if let Some(chunks) = self.get("date") {
            chunks.parse::<Date>()
        } else {
            Date::new_from_three_fields(
                self.get("year"),
                self.get("month"),
                self.get("day"),
            )
        }
    }

    fields! {
        // Fields without a specified return type simply return `&[Chunk]`.
        get_address: "address",
        get_annote: "annote",
        get_author: "author" => Vec<Person>,
        get_booktitle: "booktitle",
        get_chapter: "chapter",
        get_edition: "edition" => IntOrChunks,
        get_editor: "editor" => Vec<Person>,
        get_howpublished: "howpublished",
        get_institution: "institution",
        get_journal: "journal",
        get_note: "note",
        get_number: "number" => i64,
        get_organization: "organization",
        get_pages: "pages" => Vec<std::ops::Range<u32>>,
        get_publisher: "publisher" => Vec<Vec<Chunk>>,
        get_school: "school",
        get_series: "series",
        get_title: "title",
        get_type: "type",
        get_volume: "volume",
    }
}

/// Additional methods for chunk slices.
pub trait ChunksExt {
    /// Parse the chunks into a type.
    fn parse<T: Type>(&self) -> anyhow::Result<T>;

    /// Format the chunks in sentence case.
    fn format_sentence(&self) -> String;

    /// Format the chunks verbatim.
    fn format_verbatim(&self) -> String;
}

impl ChunksExt for [Chunk] {
    fn parse<T: Type>(&self) -> anyhow::Result<T> {
        T::parse(self)
    }

    fn format_sentence(&self) -> String {
        let mut out = String::new();
        let mut first = true;
        for val in self {
            if let Chunk::Normal(s) = val {
                for c in s.chars() {
                    if first {
                        out.push_str(&c.to_uppercase().to_string());
                    } else {
                        out.push(c);
                    }
                    first = false;
                }
            } else if let Chunk::Verbatim(s) = val {
                out += s;
            }
            first = false;
        }

        out
    }

    fn format_verbatim(&self) -> String {
        let mut out = String::new();
        for val in self {
            if let Chunk::Normal(s) = val {
                out += s;
            } else if let Chunk::Verbatim(s) = val {
                out += s;
            }
        }

        out
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

    #[test]
    fn test_gral_paper() {
        dump_debug("test/gral.bib");
    }

    #[test]
    fn test_ds_report() {
        dump_debug("test/ds.bib");
    }

    #[test]
    fn test_libra_paper() {
        dump_author_title("test/libra.bib");
    }

    #[test]
    fn test_rass_report() {
        dump_author_title("test/rass.bib");
    }

    fn dump_debug(file: &str) {
        let contents = fs::read_to_string(file).unwrap();
        let bibliography = Bibliography::from_str(&contents, true);
        println!("{:#?}", bibliography);
    }

    fn dump_author_title(file: &str) {
        let contents = fs::read_to_string(file).unwrap();
        let bibliography = Bibliography::from_str(&contents, true);

        for x in bibliography {
            let authors = x.get_author().unwrap_or_default();
            for a in authors {
                print!("{}, ", a);
            }
            println!("\"{}\".", x.get_title().unwrap().format_sentence());
        }
    }
}
