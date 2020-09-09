pub mod raw;
pub mod types;

mod resolve;

use std::collections::HashMap;

use anyhow::anyhow;

use crate::raw::RawBibliography;
use crate::resolve::resolve;
use crate::types::{Date, EditorType, Gender, IntOrChunks, Pagination, Person, Type};

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

macro_rules! alias_fields {
    ($($getter:ident: $field_name:expr, $field_alias:expr $(=> $res:ty)?),* $(,)*) => {
        $(
            #[doc = "Get and parse the `"]
            #[doc = $field_name]
            #[doc = "` field, falling back on `"]
            #[doc = $field_alias]
            #[doc = "` if `"]
            #[doc = $field_name]
            #[doc = "` is empty."]
            pub fn $getter(&self) -> anyhow::Result<fields!(@type $($res)?)> {
                self.get($field_name)
                    .or_else(|| self.get($field_alias))
                    .ok_or_else(|| anyhow!("The {} field is not present", $field_name))
                    $(.and_then(|chunks| chunks.parse::<$res>()))?
            }
        )*
    };

    (@type) => {&[Chunk]};
    (@type $res:ty) => {$res};
}

macro_rules! date_fields {
    ($($getter:ident: $field_prefix:expr),* $(,)*) => {
        $(date_fields!(
            $getter:
            concat!($field_prefix, "date"),
            concat!($field_prefix, "year"),
            concat!($field_prefix, "month"),
            concat!($field_prefix, "day")
        );)*
    };
    ($($getter:ident: $date:expr, $year:expr, $month:expr, $day:expr),* $(,)*) => {
        $(
            #[doc = "Get and parse the `"]
            #[doc = $date]
            #[doc = "` field, falling back to the `"]
            #[doc = $year]
            #[doc = "`, `"]
            #[doc = $month]
            #[doc = "`, and `"]
            #[doc = $day]
            #[doc = "` fields when not present."]
            pub fn $getter(&self) -> anyhow::Result<Date> {
                if let Some(chunks) = self.get($date) {
                    chunks.parse::<Date>()
                } else {
                    Date::new_from_three_fields(
                        self.get($year),
                        self.get($month),
                        self.get($day),
                    )
                }
            }
        )*
    };
}

impl Entry {
    fields! {
        // Fields without a specified return type simply return `&[Chunk]`.
        // BibTeX fields.
        get_author: "author" => Vec<Person>,
        get_book_title: "booktitle",
        get_chapter: "chapter",
        get_edition: "edition" => IntOrChunks,
        get_how_published: "howpublished",
        get_note: "note",
        get_number: "number",
        get_organization: "organization" => Vec<Vec<Chunk>>,
        get_pages: "pages" => Vec<std::ops::Range<u32>>,
        get_publisher: "publisher" => Vec<Vec<Chunk>>,
        get_series: "series",
        get_title: "title",
        get_type: "type",
        get_volume: "volume" => i64,
    }

    /// Get and parse the `editor` and `editora` through `editorc` fields
    /// and their respective `editortype` annotation fields.
    /// If any of the above fields is present, this function will return a
    /// vector with between one and four entries, one for each editorial role.
    ///
    /// The default `EditorType::Editor` will be assumed if the type field
    /// is empty.
    pub fn get_editors(&self) -> anyhow::Result<Vec<(Vec<Person>, EditorType)>> {
        let mut editors = vec![];

        let mut parse_editor_field = |name_field: &str, editor_field: &str| {
            self.get(name_field)
                .and_then(|chunks| chunks.parse::<Vec<Person>>().ok())
                .map(|persons| {
                    let editor_type = self
                        .get(editor_field)
                        .and_then(|chunks| chunks.parse::<EditorType>().ok())
                        .unwrap_or(EditorType::Editor);
                    editors.push((persons, editor_type));
                });
        };

        parse_editor_field("editor", "editortype");
        parse_editor_field("editora", "editoratype");
        parse_editor_field("editorb", "editorbtype");
        parse_editor_field("editorc", "editorctype");

        if editors.is_empty() {
            return Err(anyhow!("No editor fields present"));
        }

        Ok(editors)
    }

    date_fields! {
        get_date: "",
        get_event_date: "event",
        get_orig_date: "orig",
        get_url_date: "url",
    }

    alias_fields! {
        get_address: "address", "location",
        get_location: "location", "address",
        get_annotation: "annotation", "annote",
        get_eprint_type: "eprinttype", "archiveprefix",
        get_journal: "journal", "journaltitle",
        get_journal_title: "journaltitle", "journal",
        get_sort_key: "key", "sortkey" => String,
        get_file: "file", "pdf" => String,
        get_school: "school", "institution",
        get_institution: "institution", "school",
    }

    fields! {
        // BibLaTeX supplemental fields.
        get_abstract: "abstract",
        get_addendum: "addendum",
        get_afterword: "afterword" => Vec<Person>,
        get_annotator: "annotator" => Vec<Person>,
        get_author_type: "authortype" => String,
        get_book_author: "bookauthor" => Vec<Person>,
        get_book_pagination: "bookpagination" => Pagination,
        get_book_subtitle: "booksubtitle",
        get_book_title_addon: "booktitleaddon",
        get_commentator: "commentator" => Vec<Person>,
        get_doi: "doi" => String,
        get_eid: "eid",
        get_entry_subtype: "entrysubtype",
        get_eprint: "eprint" => String,
        get_eprint_class: "eprintclass",
        get_eventtitle: "eventtitle",
        get_eventtitle_addon: "eventtitleaddon",
        get_foreword: "foreword" => Vec<Person>,
        get_holder: "holder" => Vec<Person>,
        get_index_title: "indextitle",
        get_introduction: "introduction" => Vec<Person>,
        get_isan: "isan",
        get_isbn: "isbn",
        get_ismn: "ismn",
        get_isrn: "isrn",
        get_issn: "issn",
        get_issue: "issue",
        get_issue_subtitle: "issuesubtitle",
        get_issue_title: "issuetitle",
        get_issue_title_addon: "issuetitleaddon",
        get_iswc: "iswc",
        get_journal_subtitle: "journalsubtitle",
        get_journal_title_addon: "journaltitleaddon",
        get_keywords: "keywords",
        get_label: "label",
        get_language: "language" => String,
        get_library: "library",
        get_main_subtitle: "mainsubtitle",
        get_main_title: "maintitle",
        get_main_title_addon: "maintitleaddon",
        get_name_addon: "nameaddon",
        get_options: "options",
        get_orig_language: "origlanguage" => String,
        get_orig_location: "origlocation",
        get_page_total: "pagetotal",
        get_pagination: "pagination" => Pagination,
        get_part: "part",
        get_pubstate: "pubstate",
        get_reprint_title: "reprinttitle",
        get_short_author: "shortauthor" => Vec<Person>,
        get_short_editor: "shorteditor" => Vec<Person>,
        get_shorthand: "shorthand",
        get_short_series: "shortseries",
        get_short_title: "shorttitle",
        get_subtitle: "subtitle",
        get_title_addon: "titleaddon",
        get_translator: "translator" => Vec<Person>,
        get_url: "url" => String,
        get_venue: "venue",
        get_version: "version",
        get_volumes: "volumes" => i64,
        get_gender: "gender" => Gender,
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
