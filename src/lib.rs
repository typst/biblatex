pub mod raw;
pub mod types;

mod resolve;

use std::collections::HashMap;

use anyhow::anyhow;
use paste::paste;

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
    /// Get a new, empty Bibliography
    pub fn new() -> Self {
        Self(Vec::new())
    }

    /// Parse a bibliography from a source string.
    pub fn from_str(src: &str, allow_bibtex: bool) -> Self {
        Self::from_raw(RawBibliography::from_str(src, allow_bibtex))
    }

    /// Parse a bibliography from a raw bibliography.
    pub fn from_raw(raw: RawBibliography) -> Self {
        let mut res = Self::new();
        let abbreviations = &raw.abbreviations;

        for entry in raw.entries {
            res.add(Entry {
                cite_key: entry.cite_key.to_string(),
                entry_type: entry.entry_type.to_lowercase().to_string(),
                fields: entry
                    .fields
                    .into_iter()
                    .map(|(key, value)| (key.to_string(), resolve(value, abbreviations)))
                    .collect(),
            })
            .ok();
        }

        res
    }

    /// Try to find an entry with the given cite key.
    pub fn get(&self, cite_key: &str) -> Option<&Entry> {
        self.0.iter().find(|entry| entry.cite_key == cite_key)
    }

    /// Try to find an entry with the given cite key and return a mutable reference.
    pub fn get_mut(&mut self, cite_key: &str) -> Option<&mut Entry> {
        self.0.iter_mut().find(|entry| entry.cite_key == cite_key)
    }

    /// Add a new entry of that type to the bibliography if the cite key
    /// is not already in use.
    pub fn add(&mut self, entry: Entry) -> anyhow::Result<()> {
        if self.get(&entry.cite_key).is_some() {
            Err(anyhow!("key already present"))
        } else {
            self.0.push(entry);
            Ok(())
        }
    }

    /// Add a new entry of that type to the bibliography if the cite key
    /// is not already in use.
    pub fn add_empty(
        &mut self,
        cite_key: &str,
        entry_type: &str,
    ) -> anyhow::Result<&mut Entry> {
        if self.get(cite_key).is_some() {
            Err(anyhow!("key already present"))
        } else {
            self.0.push(Entry::new(cite_key, entry_type));
            self.get_mut(cite_key)
                .ok_or_else(|| anyhow!("could not fetch inserted entry"))
        }
    }

    ///
    pub fn len(&self) -> usize {
        self.0.len()
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
    /// Construct new, empty entry.
    pub fn new(cite_key: &str, entry_type: &str) -> Self {
        Self {
            cite_key: cite_key.to_string(),
            entry_type: entry_type.to_string(),
            fields: HashMap::new(),
        }
    }

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

    /// Sets a field value as a chunk vector.
    pub fn set(&mut self, key: &str, chunks: Vec<Chunk>) {
        self.fields.insert(key.to_lowercase(), chunks);
    }

    /// Sets a field value as a chunk vector as a specific type.
    pub fn set_as<T: Type>(&mut self, key: &str, value: &T) -> anyhow::Result<()> {
        let chunks = value.to_chunks()?;
        self.fields.insert(key.to_lowercase(), chunks);
        Ok(())
    }
}

macro_rules! fields {
    ($($name:ident: $field_name:expr $(=> $res:ty)?),* $(,)*) => {
        $(
            paste! {
                #[doc = "Get and parse the `" $field_name "` field."]
                pub fn [<get_ $name>](&self) -> anyhow::Result<fields!(@type $($res)?)> {
                    self.get($field_name)
                        .ok_or_else(|| anyhow!("The {} field is not present", $field_name))
                        $(.and_then(|chunks| chunks.parse::<$res>()))?
                }

                fields!(single_set $name => $field_name, $($res)?);
            }
        )*
    };

    (single_set $name:ident => $field_name:expr, ) => {
        paste! {
            #[doc = "Set a value in the `" $field_name "` field."]
            pub fn [<set_ $name>](&mut self, item: Vec<Chunk>) -> anyhow::Result<()> {
                self.set($field_name, item);
                Ok(())
            }
        }
    };
    (single_set $name:ident => $field_name:expr, $other_type:ty) => {
        paste! {
            #[doc = "Set a value in the `" $field_name "` field."]
            pub fn [<set_ $name>](&mut self, item: $other_type) -> anyhow::Result<()> {
                let chunks = item.to_chunks()?;
                self.set($field_name, chunks);
                Ok(())
            }
        }
    };

    (@type) => {&[Chunk]};
    (@type $res:ty) => {$res};
}

macro_rules! alias_fields {
    ($($name:ident: $field_name:expr, $field_alias:expr $(=> $res:ty)?),* $(,)*) => {
        $(
            paste! {
                #[doc = "Get and parse the `" $field_name "` field, falling back on `" $field_alias "` if `" $field_name "` is empty."]
                pub fn [<get_ $name>](&self) -> anyhow::Result<fields!(@type $($res)?)> {
                    self.get($field_name)
                        .or_else(|| self.get($field_alias))
                        .ok_or_else(|| anyhow!("The {} field is not present", $field_name))
                        $(.and_then(|chunks| chunks.parse::<$res>()))?
                }

                fields!(single_set $name => $field_name, $($res)?);
            }
        )*
    };

    (@type) => {&[Chunk]};
    (@type $res:ty) => {$res};
}

macro_rules! date_fields {
    ($($name:ident: $field_prefix:expr),* $(,)*) => {
        $(
            paste! {
                #[doc = "Get and parse the `" $field_prefix "date` field, falling back to the `" $field_prefix "year`, `" $field_prefix "month`, and `" $field_prefix "day` fields when not present."]
                pub fn [<get_ $name>](&self) -> anyhow::Result<Date> {
                    if let Some(chunks) = self.get(concat!($field_prefix, "date")) {
                        chunks.parse::<Date>()
                    } else {
                        Date::new_from_three_fields(
                            self.get(concat!($field_prefix, "year")),
                            self.get(concat!($field_prefix, "month")),
                            self.get(concat!($field_prefix, "day")),
                        )
                    }
                }

                #[doc = "Set a value in the `" $field_prefix "date` field."]
                pub fn [<set_ $name>](&mut self, item: Date) -> anyhow::Result<()> {
                    let chunks = item.to_chunks()?;
                    self.set(concat!($field_prefix, "date"), chunks);
                    Ok(())
                }
            }
        )*
    };
}

impl Entry {
    fields! {
        // Fields without a specified return type simply return `&[Chunk]`.
        // BibTeX fields.
        author: "author" => Vec<Person>,
        book_title: "booktitle",
        chapter: "chapter",
        edition: "edition" => IntOrChunks,
        how_published: "howpublished",
        note: "note",
        number: "number",
        organization: "organization" => Vec<Vec<Chunk>>,
        pages: "pages" => Vec<std::ops::Range<u32>>,
        publisher: "publisher" => Vec<Vec<Chunk>>,
        series: "series",
        title: "title",
        type: "type" => String,
        volume: "volume" => i64,
    }

    date_fields! {
        date: "",
        event_date: "event",
        orig_date: "orig",
        url_date: "url",
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

    alias_fields! {
        address: "address", "location",
        location: "location", "address",
        annotation: "annotation", "annote",
        eprint_type: "eprinttype", "archiveprefix",
        journal: "journal", "journaltitle",
        journal_title: "journaltitle", "journal",
        sort_key: "key", "sortkey" => String,
        file: "file", "pdf" => String,
        school: "school", "institution",
        institution: "institution", "school",
    }

    fields! {
        // BibLaTeX supplemental fields.
        abstract: "abstract",
        addendum: "addendum",
        afterword: "afterword" => Vec<Person>,
        annotator: "annotator" => Vec<Person>,
        author_type: "authortype" => String,
        book_author: "bookauthor" => Vec<Person>,
        book_pagination: "bookpagination" => Pagination,
        book_subtitle: "booksubtitle",
        book_title_addon: "booktitleaddon",
        commentator: "commentator" => Vec<Person>,
        doi: "doi" => String,
        eid: "eid",
        entry_subtype: "entrysubtype",
        eprint: "eprint" => String,
        eprint_class: "eprintclass",
        eventtitle: "eventtitle",
        eventtitle_addon: "eventtitleaddon",
        foreword: "foreword" => Vec<Person>,
        holder: "holder" => Vec<Person>,
        index_title: "indextitle",
        introduction: "introduction" => Vec<Person>,
        isan: "isan",
        isbn: "isbn",
        ismn: "ismn",
        isrn: "isrn",
        issn: "issn",
        issue: "issue",
        issue_subtitle: "issuesubtitle",
        issue_title: "issuetitle",
        issue_title_addon: "issuetitleaddon",
        iswc: "iswc",
        journal_subtitle: "journalsubtitle",
        journal_title_addon: "journaltitleaddon",
        keywords: "keywords",
        label: "label",
        language: "language" => String,
        library: "library",
        main_subtitle: "mainsubtitle",
        main_title: "maintitle",
        main_title_addon: "maintitleaddon",
        name_addon: "nameaddon",
        options: "options",
        orig_language: "origlanguage" => String,
        orig_location: "origlocation",
        page_total: "pagetotal",
        pagination: "pagination" => Pagination,
        part: "part",
        pubstate: "pubstate",
        reprint_title: "reprinttitle",
        short_author: "shortauthor" => Vec<Person>,
        short_editor: "shorteditor" => Vec<Person>,
        shorthand: "shorthand",
        shorthand_intro: "shorthandintro",
        short_journal: "shortjournal",
        short_series: "shortseries",
        short_title: "shorttitle",
        subtitle: "subtitle",
        title_addon: "titleaddon",
        translator: "translator" => Vec<Person>,
        url: "url" => String,
        venue: "venue",
        version: "version",
        volumes: "volumes" => i64,
        gender: "gender" => Gender,
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
        T::from_chunks(self)
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
        println!("{:#?}", bibliography.0);
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
