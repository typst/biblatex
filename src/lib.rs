/*!
A crate for parsing Bib(La)TeX files.

The main API entrypoint is the [`Bibliography`] struct.

# Example

Finding out the author of a work.
```
# use biblatex::Bibliography;
# fn main() -> std::io::Result<()> {
let src = "@book{tolkien1937, author = {J. R. R. Tolkien}}";
let bibliography = Bibliography::parse(src).unwrap();
let entry = bibliography.get("tolkien1937").unwrap();
let author = entry.author().unwrap();
assert_eq!(author[0].name, "Tolkien");
# Ok(())
# }
```
*/

#![deny(missing_docs)]

mod chunk;
mod macros;
mod mechanics;
mod raw;
mod resolve;
mod types;

pub use chunk::{Chunk, Chunks, ChunksExt, ChunksRef};
pub use mechanics::EntryType;
pub use raw::{
    Field, Pair, ParseError, ParseErrorKind, RawBibliography, RawChunk, RawEntry, Token,
};
pub use types::*;

use std::collections::BTreeMap;
use std::fmt;
use std::fmt::{Debug, Display, Formatter, Write};

use macros::*;
use mechanics::{is_verbatim_field, AuthorMode, PagesChapterMode};

use paste::paste;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A fully parsed bibliography.
#[derive(Debug, Clone, Default, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Bibliography {
    /// The bibliography entries.
    entries: Vec<Entry>,
    /// Maps from citation keys to indices in `items`.
    keys: BTreeMap<String, usize>,
}

/// A bibliography entry containing chunk fields, which can be parsed into more
/// specific types on demand.
#[derive(Debug, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Entry {
    /// The citation key.
    pub key: String,
    /// Denotes the type of bibliography item (e.g., `Article`).
    pub entry_type: EntryType,
    /// Maps from field names to their associated chunk vectors.
    pub fields: BTreeMap<String, Chunks>,
}

/// Errors that can occur when retrieving a field of an [`Entry`].
#[derive(Debug, Clone, PartialEq)]
pub enum RetrievalError {
    /// The entry has no field with this name.
    Missing(String),
    /// The field contains malformed data.
    TypeError(TypeError),
}

impl Display for RetrievalError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Missing(s) => write!(f, "field {} is missing", s),
            Self::TypeError(err) => write!(f, "{}", err),
        }
    }
}

impl From<TypeError> for RetrievalError {
    fn from(err: TypeError) -> Self {
        Self::TypeError(err)
    }
}

fn convert_result<T>(err: Result<T, RetrievalError>) -> Result<Option<T>, TypeError> {
    match err {
        Ok(val) => Ok(Some(val)),
        Err(RetrievalError::Missing(_)) => Ok(None),
        Err(RetrievalError::TypeError(err)) => Err(err),
    }
}

impl Bibliography {
    /// Create a new, empty bibliography.
    pub fn new() -> Self {
        Self::default()
    }

    /// Parse a bibliography from a source string.
    pub fn parse(src: &str) -> Result<Self, ParseError> {
        Self::from_raw(RawBibliography::parse(src)?)
    }

    /// Construct a bibliography from a raw bibliography, with the `xdata` and
    /// `crossref` links resolved.
    pub fn from_raw(raw: RawBibliography) -> Result<Self, ParseError> {
        let mut res = Self::new();
        let abbr = &raw.abbreviations;

        for entry in raw.entries {
            // Check that the key is not repeated
            if res.get(entry.v.key.v).is_some() {
                return Err(ParseError::new(
                    entry.span,
                    ParseErrorKind::DuplicateKey(entry.v.key.v.to_string()),
                ));
            }

            let mut fields: BTreeMap<String, Vec<Spanned<Chunk>>> = BTreeMap::new();
            for spanned_field in entry.v.fields.into_iter() {
                let field_key = spanned_field.key.v.to_string().to_ascii_lowercase();
                let parsed =
                    resolve::parse_field(&field_key, &spanned_field.value.v, abbr)?;
                fields.insert(field_key, parsed);
            }
            res.insert(Entry {
                key: entry.v.key.v.to_string(),
                entry_type: EntryType::new(entry.v.kind.v),
                fields,
            });
        }

        let mut entries = res.entries.clone();
        for entry in &mut entries {
            entry.resolve_crossrefs(&res).map_err(|e| {
                ParseError::new(e.span, ParseErrorKind::ResolutionError(e.kind))
            })?;
        }
        res.entries = entries;

        Ok(res)
    }

    /// The number of bibliography entries.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the bibliography is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Returns the entry with the given cite key.
    pub fn get(&self, key: &str) -> Option<&Entry> {
        let index = *self.keys.get(key)?;
        self.entries.get(index)
    }

    /// Returns a mutable reference to the entry with the given cite key.
    pub fn get_mut(&mut self, key: &str) -> Option<&mut Entry> {
        let index = *self.keys.get(key)?;
        self.entries.get_mut(index)
    }

    /// Insert an entry into the bibliography.
    ///
    /// If an entry with the same cite key is already present, the entry is
    /// updated and the old entry is returned.
    pub fn insert(&mut self, entry: Entry) -> Option<Entry> {
        if let Some(prev) = self.get_mut(&entry.key) {
            Some(std::mem::replace(prev, entry))
        } else {
            let index = self.entries.len();
            self.keys.insert(entry.key.clone(), index);
            if let Some(ids) = convert_result(entry.get_as::<Vec<String>>("ids")).unwrap()
            {
                for alias in ids {
                    self.keys.insert(alias, index);
                }
            }
            self.entries.push(entry);
            None
        }
    }

    /// Remove the entry with the given cite key.
    pub fn remove(&mut self, key: &str) -> Option<Entry> {
        let index = *self.keys.get(key)?;
        let entry = self.entries.remove(index);

        // Remove equal indices and update later indices.
        self.keys.retain(|_, v| {
            if *v > index {
                *v -= 1;
                true
            } else {
                *v != index
            }
        });

        Some(entry)
    }

    /// Add an alias for a cite key.
    ///
    /// Does nothing if no entry with the given cite key exists.
    pub fn alias(&mut self, key: &str, alias: impl Into<String>) {
        if let Some(&index) = self.keys.get(key) {
            self.keys.insert(alias.into(), index);
        }
    }

    /// An iterator over the bibliography's entries.
    pub fn iter(&self) -> std::slice::Iter<Entry> {
        self.entries.iter()
    }

    /// A mutable iterator over the bibliography's entries.
    pub fn iter_mut(&mut self) -> std::slice::IterMut<Entry> {
        self.entries.iter_mut()
    }

    /// Consume this struct and return a vector of the bibliography's entries.
    pub fn into_vec(self) -> Vec<Entry> {
        self.entries
    }

    /// Write the entry into a writer in the BibLaTeX format.
    pub fn write_biblatex(&self, mut sink: impl Write) -> fmt::Result {
        let mut first = true;
        for entry in &self.entries {
            if !first {
                writeln!(sink)?;
            }
            writeln!(sink, "{}", entry.to_biblatex_string())?;
            first = false;
        }
        Ok(())
    }

    /// Serialize this bibliography into a BibLaTeX string.
    pub fn to_biblatex_string(&self) -> String {
        let mut biblatex = String::new();
        self.write_biblatex(&mut biblatex).unwrap();
        biblatex
    }

    /// Write the entry into a writer in the BibTeX format.
    pub fn write_bibtex(&self, mut sink: impl Write) -> fmt::Result {
        let mut first = true;
        for entry in &self.entries {
            if !first {
                writeln!(sink)?;
            }
            writeln!(sink, "{}", entry.to_bibtex_string().map_err(|_| fmt::Error)?)?;
            first = false;
        }
        Ok(())
    }

    /// Serialize this bibliography into a BibTeX string.
    pub fn to_bibtex_string(&self) -> String {
        let mut bibtex = String::new();
        self.write_bibtex(&mut bibtex).unwrap();
        bibtex
    }
}

impl IntoIterator for Bibliography {
    type Item = Entry;
    type IntoIter = std::vec::IntoIter<Entry>;

    fn into_iter(self) -> Self::IntoIter {
        self.entries.into_iter()
    }
}

impl Entry {
    /// Construct new, empty entry.
    pub fn new(key: String, entry_type: EntryType) -> Self {
        Self { key, entry_type, fields: BTreeMap::new() }
    }

    /// Get the chunk slice of a field.
    ///
    /// The field key must be lowercase.
    pub fn get(&self, key: &str) -> Option<ChunksRef> {
        self.fields.get(key).map(AsRef::as_ref)
    }

    /// Parse the value of a field into a specific type.
    ///
    /// The field key must be lowercase.
    pub fn get_as<T: Type>(&self, key: &str) -> Result<T, RetrievalError> {
        self.get(key)
            .ok_or_else(|| RetrievalError::Missing(key.to_string()))?
            .parse::<T>()
            .map_err(Into::into)
    }

    /// Set the chunk slice for a field.
    ///
    /// The field key is lowercase before insertion.
    pub fn set(&mut self, key: &str, chunks: Chunks) {
        self.fields.insert(key.to_lowercase(), chunks);
    }

    /// Set the value of a field as a specific type.
    ///
    /// The field key is lowercase before insertion.
    pub fn set_as<T: Type>(&mut self, key: &str, value: &T) {
        self.set(key, value.to_chunks());
    }

    /// Remove a field from the entry.
    pub fn remove(&mut self, key: &str) -> Option<Chunks> {
        self.fields.remove(key)
    }

    /// The parents of an entry in a semantic sense (`crossref` and `xref`).
    pub fn parents(&self) -> Result<Vec<String>, TypeError> {
        let mut parents = vec![];

        if let Some(crossref) = convert_result(self.get_as::<String>("crossref"))? {
            parents.push(crossref);
        }

        if let Some(xrefs) = convert_result(self.get_as::<Vec<String>>("xref"))? {
            parents.extend(xrefs);
        }

        Ok(parents)
    }

    /// Verify if the entry has the appropriate fields for its [`EntryType`].
    pub fn verify(&self) -> Report {
        let reqs = self.entry_type.requirements();
        let mut missing = vec![];
        let mut superfluous = vec![];

        for field in reqs.required {
            match field {
                "journaltitle" => {
                    if self
                        .get_non_empty(field)
                        .or_else(|| self.get_non_empty("journal"))
                        .is_none()
                    {
                        missing.push(field);
                    }
                }
                "location" => {
                    if self
                        .get_non_empty(field)
                        .or_else(|| self.get_non_empty("address"))
                        .is_none()
                    {
                        missing.push(field);
                    }
                }
                "school"
                    if self.entry_type == EntryType::Thesis
                        || self.entry_type == EntryType::MastersThesis
                        || self.entry_type == EntryType::PhdThesis =>
                {
                    if self
                        .get_non_empty(field)
                        .or_else(|| self.get_non_empty("institution"))
                        .is_none()
                    {
                        missing.push(field);
                    }
                }
                _ => {
                    if self.get_non_empty(field).is_none() {
                        missing.push(field);
                    }
                }
            }
        }

        for field in reqs.forbidden {
            if self.get_non_empty(field).is_some() {
                superfluous.push(field);
            }
        }

        match reqs.author_eds_field {
            AuthorMode::OneRequired => {
                if self.author().is_err() && self.editors().unwrap_or_default().is_empty()
                {
                    missing.push("author");
                }
            }
            AuthorMode::BothRequired => {
                if self.editors().unwrap_or_default().is_empty() {
                    missing.push("editor");
                }
                if self.author().is_err() {
                    missing.push("author");
                }
            }
            AuthorMode::AuthorRequired | AuthorMode::AuthorRequiredEditorOptional => {
                if self.author().is_err() {
                    missing.push("author");
                }
            }
            AuthorMode::EditorRequiredAuthorForbidden => {
                if self.editors().unwrap_or_default().is_empty() {
                    missing.push("editor");
                }
                if self.author().is_ok() {
                    superfluous.push("author");
                }
            }
            _ => {}
        }

        match reqs.page_chapter_field {
            PagesChapterMode::OneRequired => {
                if self.pages().is_err() && self.chapter().is_err() {
                    missing.push("pages");
                }
            }
            PagesChapterMode::BothForbidden => {
                if self.pages().is_ok() {
                    superfluous.push("pages");
                }
                if self.chapter().is_ok() {
                    superfluous.push("chapter");
                }
            }
            PagesChapterMode::PagesRequired => {
                if self.pages().is_err() {
                    missing.push("pages");
                }
            }
            _ => {}
        }

        let mut malformed = vec![];

        for (key, chunks) in &self.fields {
            let error = match key.as_str() {
                "edition" => chunks.parse::<PermissiveType<i64>>().err(),
                "organization" => chunks.parse::<Vec<Chunks>>().err(),
                "pages" => chunks.parse::<Vec<std::ops::Range<u32>>>().err(),
                "publisher" => chunks.parse::<Vec<Chunks>>().err(),
                "volume" => chunks.parse::<i64>().err(),
                "bookpagination" => chunks.parse::<Pagination>().err(),
                "pagination" => chunks.parse::<Pagination>().err(),
                "volumes" => chunks.parse::<i64>().err(),
                "gender" => chunks.parse::<Gender>().err(),
                "editortype" => chunks.parse::<EditorType>().err(),
                "editoratype" => chunks.parse::<EditorType>().err(),
                "editorbtype" => chunks.parse::<EditorType>().err(),
                "editorctype" => chunks.parse::<EditorType>().err(),
                "xref" => chunks.parse::<Vec<String>>().err(),
                "xdata" => chunks.parse::<Vec<String>>().err(),
                "ids" => chunks.parse::<Vec<String>>().err(),
                _ => continue,
            };

            if let Some(err) = error {
                malformed.push((key.clone(), err))
            }
        }

        for (key, err) in [
            ("date", self.date().err()),
            ("urldate", self.url_date().err()),
            ("origdate", self.orig_date().err()),
            ("eventdate", self.event_date().err()),
        ] {
            if let Some(RetrievalError::TypeError(t)) = err {
                malformed.push((key.to_string(), t));
            }
        }

        if reqs.needs_date {
            if let Err(RetrievalError::Missing(_)) = self.date() {
                missing.push("year");
            }
        }

        Report { missing, superfluous, malformed }
    }

    /// Serialize this entry into a BibLaTeX string.
    pub fn to_biblatex_string(&self) -> String {
        let mut biblatex = String::new();
        let ty = self.entry_type.to_biblatex();

        writeln!(biblatex, "@{}{{{},", ty, self.key).unwrap();

        for (key, value) in &self.fields {
            let key = match key.as_ref() {
                "journal" => "journaltitle",
                "address" => "location",
                "school" => "institution",
                k => k,
            };

            writeln!(
                biblatex,
                "{} = {},",
                key,
                value.to_biblatex_string(is_verbatim_field(key))
            )
            .unwrap();
        }

        biblatex.push('}');
        biblatex
    }

    /// Serialize this entry into a BibTeX string.
    ///
    /// This function can return an error if there is a malformed date field.
    pub fn to_bibtex_string(&self) -> Result<String, TypeError> {
        let mut bibtex = String::new();
        let ty = self.entry_type.to_bibtex();
        let thesis = matches!(ty, EntryType::PhdThesis | EntryType::MastersThesis);

        writeln!(bibtex, "@{}{{{},", ty, self.key).unwrap();

        for (key, value) in &self.fields {
            if key == "date" {
                if let Some(date) = convert_result(self.date())? {
                    if let PermissiveType::Typed(date) = date {
                        for (key, value) in date.to_fieldset() {
                            let v = [Spanned::zero(Chunk::Normal(value))]
                                .to_biblatex_string(false);
                            writeln!(bibtex, "{} = {},", key, v).unwrap();
                        }
                        continue;
                    }
                } else {
                    continue;
                }
            }

            let key = match key.as_ref() {
                "journaltitle" => "journal",
                "location" => "address",
                "institution" if thesis => "school",
                k => k,
            };

            writeln!(
                bibtex,
                "{} = {},",
                key,
                value.to_biblatex_string(is_verbatim_field(key))
            )
            .unwrap();
        }

        bibtex.push('}');
        Ok(bibtex)
    }

    /// Get an entry but return None for empty chunk slices.
    fn get_non_empty(&self, key: &str) -> Option<ChunksRef> {
        let entry = self.get(key)?;
        if !entry.is_empty() {
            Some(entry)
        } else {
            None
        }
    }

    /// Resolves all data dependencies defined by `crossref` and `xdata` fields.
    fn resolve_crossrefs(&mut self, bib: &Bibliography) -> Result<(), TypeError> {
        let mut refs = vec![];

        if let Some(crossref) = convert_result(self.get_as::<String>("crossref"))? {
            refs.extend(bib.get(&crossref).cloned());
        }

        if let Some(keys) = convert_result(self.get_as::<Vec<String>>("xdata"))? {
            for key in keys {
                refs.extend(bib.get(&key).cloned());
            }
        }

        for mut crossref in refs {
            crossref.resolve_crossrefs(bib)?;
            self.resolve_single_crossref(crossref)?;
        }

        self.remove("xdata");

        Ok(())
    }

    /// Resolve data dependencies using another entry.
    fn resolve_single_crossref(&mut self, crossref: Entry) -> Result<(), TypeError> {
        let req = self.entry_type.requirements();

        let mut relevant = req.required;
        relevant.extend(req.optional);
        relevant.extend(req.page_chapter_field.possible());
        relevant.extend(req.author_eds_field.possible());

        if self.entry_type == EntryType::XData {
            for f in crossref.fields.keys() {
                relevant.push(f);
            }
        }

        for f in relevant {
            if self.get(f).is_some() {
                continue;
            }

            match f {
                "journaltitle" | "journalsubtitle"
                    if crossref.entry_type == EntryType::Periodical =>
                {
                    let key = if f.contains('s') { "subtitle" } else { "title" };

                    if let Some(item) = crossref.get(key) {
                        self.set(f, item.to_vec())
                    }
                }
                "booktitle" | "booksubtitle" | "booktitleaddon"
                    if crossref.entry_type.is_collection() =>
                {
                    let key = if f.contains('s') {
                        "subtitle"
                    } else if f.contains('a') {
                        "titleaddon"
                    } else {
                        "title"
                    };

                    if let Some(item) = crossref.get(key) {
                        self.set(f, item.to_vec())
                    }
                }
                "maintitle" | "mainsubtitle" | "maintitleaddon"
                    if crossref.entry_type.is_multi_volume() =>
                {
                    let key = if f.contains('s') {
                        "subtitle"
                    } else if f.contains('a') {
                        "titleaddon"
                    } else {
                        "title"
                    };

                    if let Some(item) = crossref.get(key) {
                        self.set(f, item.to_vec())
                    }
                }
                "address" => {
                    if let Some(item) =
                        crossref.get(f).or_else(|| crossref.get("location"))
                    {
                        self.set(f, item.to_vec())
                    }
                }
                "institution" => {
                    if let Some(item) = crossref.get(f).or_else(|| crossref.get("school"))
                    {
                        self.set(f, item.to_vec())
                    }
                }
                "school" => {
                    if let Some(item) =
                        crossref.get(f).or_else(|| crossref.get("institution"))
                    {
                        self.set(f, item.to_vec())
                    }
                }
                "journaltitle" => {
                    if let Some(item) =
                        crossref.get(f).or_else(|| crossref.get("journal"))
                    {
                        self.set(f, item.to_vec())
                    }
                }
                "title" | "addendum" | "note" => {}
                _ => {
                    if let Some(item) = crossref.get(f) {
                        self.set(f, item.to_vec())
                    }
                }
            }
        }

        if self.entry_type == EntryType::XData {
            return Ok(());
        }

        if req.needs_date {
            if let Some(date) = convert_result(crossref.date())? {
                self.set_date(date);
            }
        }

        Ok(())
    }
}

/// A report of the validity of an `Entry`. Can be obtained by calling [`Entry::verify`].
pub struct Report {
    /// These fields were missing, although they are required for the entry type.
    pub missing: Vec<&'static str>,
    /// These fields were present but are not allowed for the entry type.
    pub superfluous: Vec<&'static str>,
    /// These fields were present but contained malformed data.
    pub malformed: Vec<(String, TypeError)>,
}

impl Report {
    /// Whether the report is empty and contains no errors.
    pub fn is_ok(&self) -> bool {
        self.missing.is_empty()
            && self.superfluous.is_empty()
            && self.malformed.is_empty()
    }
}

impl Entry {
    // BibTeX fields.
    fields! {
        // Fields without a specified return type simply return `ChunksRef`.
        author: "author" => Vec<Person>,
        book_title: "booktitle",
        chapter: "chapter",
        edition: "edition" => PermissiveType<i64>,
        how_published: "howpublished",
        note: "note",
        number: "number",
        organization: "organization" => Vec<Chunks>,
        pages: "pages" => PermissiveType<Vec<std::ops::Range<u32>>>,
        publisher: "publisher" => Vec<Chunks>,
        series: "series",
        title: "title",
        type_: "type" => String,
        volume: "volume" => PermissiveType<i64>,
    }

    alias_fields! {
        address: "address" | "location",
        location: "location" | "address",
        annotation: "annotation" | "annote",
        eprint_type: "eprinttype" | "archiveprefix",
        journal: "journal" | "journaltitle",
        journal_title: "journaltitle" | "journal",
        sort_key: "key" | "sortkey" => String,
        file: "file" | "pdf" => String,
        school: "school" | "institution",
        institution: "institution" | "school",
    }

    date_fields! {
        date: "",
        event_date: "event",
        orig_date: "orig",
        url_date: "url",
    }

    /// Get the `editor` and `editora` through `editorc` fields and their
    /// respective `editortype` annotation fields, returning a vector with zero
    /// to four entries, one for each editorial role.
    ///
    /// The default `EditorType::Editor` is assumed if the type field is empty.
    pub fn editors(&self) -> Result<Vec<(Vec<Person>, EditorType)>, TypeError> {
        let mut editors = vec![];

        let mut parse = |name_field: &str, editor_field: &str| -> Result<(), TypeError> {
            if let Some(persons) = convert_result(self.get_as::<Vec<Person>>(name_field))?
            {
                let editor_type = self
                    .get(editor_field)
                    .map(|chunks| chunks.parse::<EditorType>())
                    .transpose()?
                    .unwrap_or(EditorType::Editor);
                editors.push((persons, editor_type));
            }

            Ok(())
        };

        parse("editor", "editortype")?;
        parse("editora", "editoratype")?;
        parse("editorb", "editorbtype")?;
        parse("editorc", "editorctype")?;

        Ok(editors)
    }

    // BibLaTeX supplemental fields.
    fields! {
        abstract_: "abstract",
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

type Span = std::ops::Range<usize>;

/// A value with the span it corresponds to in the source code.
///
/// Spans can be _detached,_ this means that they deliberately do not point
/// into the source code. Such spans are created when manually setting fields
/// with an empty bibliography or after parsing a file. Detached spans do not
/// indicate valid index ranges in the source files and must not be used as
/// such. A spanned item can be checked for detachment by calling
/// [`Self::is_detached`].
#[derive(Clone, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Spanned<T> {
    /// The spanned value.
    pub v: T,
    /// The location in source code of the value.
    pub span: Span,
}

impl<T> Spanned<T> {
    /// Create a new instance from a value and its span.
    pub fn new(v: T, span: Span) -> Self {
        Self { v, span }
    }

    /// Create a new instance with a value and a zero-length span.
    pub fn zero(v: T) -> Self {
        Self { v, span: 0..0 }
    }

    /// Create a new instance with a detached span.
    pub fn detached(v: T) -> Self {
        Self { v, span: usize::MAX..usize::MAX }
    }

    /// Whether the span is detached.
    pub fn is_detached(&self) -> bool {
        self.span.start == usize::MAX
    }

    /// Convert from `&Spanned<T>` to `Spanned<&T>`
    pub fn as_ref(&self) -> Spanned<&T> {
        Spanned { v: &self.v, span: self.span.clone() }
    }

    /// Map the value using a function keeping the span.
    pub fn map<F, U>(self, f: F) -> Spanned<U>
    where
        F: FnOnce(T) -> U,
    {
        Spanned { v: f(self.v), span: self.span }
    }
}

impl<T: Debug> Debug for Spanned<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.v.fmt(f)?;
        if f.alternate() {
            f.write_str(" <")?;
            self.span.fmt(f)?;
            f.write_str(">")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;
    use crate::raw::Token;

    #[test]
    fn test_correct_bib() {
        let contents = fs::read_to_string("tests/gral.bib").unwrap();
        let bibliography = Bibliography::parse(&contents).unwrap();
        assert_eq!(bibliography.entries.len(), 83)
    }

    #[test]
    fn test_repeated_key() {
        let contents = fs::read_to_string("tests/gral_rep_key.bib").unwrap();
        let bibliography = Bibliography::parse(&contents);
        match bibliography {
            Ok(_) => panic!("Should return Err"),
            Err(s) => {
                assert_eq!(s.kind, ParseErrorKind::DuplicateKey("ishihara2012".into()));
            }
        };
    }

    #[test]
    fn test_parse_incorrect_result() {
        let contents = fs::read_to_string("tests/incorrect_syntax.bib").unwrap();

        let bibliography = Bibliography::parse(&contents);
        match bibliography {
            Ok(_) => {
                panic!("Should return Err")
            }
            Err(s) => {
                assert_eq!(
                    s,
                    ParseError::new(369..369, ParseErrorKind::Expected(Token::Equals))
                );
            }
        };
    }

    #[test]
    fn test_parse_incorrect_types() {
        let contents = fs::read_to_string("tests/incorrect_data.bib").unwrap();

        let bibliography = Bibliography::parse(&contents).unwrap();
        let rashid = bibliography.get("rashid2016").unwrap();
        match rashid.pagination() {
            Err(RetrievalError::TypeError(s)) => {
                assert_eq!(s, TypeError::new(352..359, TypeErrorKind::UnknownPagination));
            }
            _ => {
                panic!()
            }
        };
    }

    #[test]
    fn test_gral_paper() {
        dump_debug("tests/gral.bib");
    }

    #[test]
    fn test_ds_report() {
        dump_debug("tests/ds.bib");
    }

    #[test]
    fn test_libra_paper() {
        dump_author_title("tests/libra.bib");
    }

    #[test]
    fn test_rass_report() {
        dump_author_title("tests/rass.bib");
    }

    #[test]
    fn test_polar_report() {
        dump_author_title("tests/polaritons.bib");
    }

    #[test]
    fn test_extended_name_format() {
        dump_author_title("tests/extended_name_format.bib");
    }

    #[test]
    fn test_alias() {
        let contents = fs::read_to_string("tests/cross.bib").unwrap();
        let mut bibliography = Bibliography::parse(&contents).unwrap();

        assert_eq!(bibliography.get("issue201"), bibliography.get("github"));
        bibliography.alias("issue201", "crap");
        assert_eq!(bibliography.get("crap"), bibliography.get("unstable"));
        bibliography.remove("crap").unwrap();

        let entry = bibliography.get("cannonfodder").unwrap();
        assert_eq!(entry.key, "cannonfodder");
        assert_eq!(entry.entry_type, EntryType::Misc);
    }

    #[test]
    fn test_bibtex_conversion() {
        let contents = fs::read_to_string("tests/cross.bib").unwrap();
        let mut bibliography = Bibliography::parse(&contents).unwrap();

        let biblatex = bibliography.get_mut("haug2019").unwrap().to_biblatex_string();
        assert!(biblatex.contains("institution = {Technische Universität Berlin},"));

        let bibtex =
            bibliography.get_mut("haug2019").unwrap().to_bibtex_string().unwrap();
        assert!(bibtex.contains("school = {Technische Universität Berlin},"));
        assert!(bibtex.contains("year = {2019},"));
        assert!(bibtex.contains("month = {10},"));
        assert!(!bibtex.contains("institution"));
        assert!(!bibtex.contains("date"));
    }

    #[test]
    fn test_verify() {
        let contents = fs::read_to_string("tests/cross.bib").unwrap();
        let mut bibliography = Bibliography::parse(&contents).unwrap();

        assert!(bibliography.get_mut("haug2019").unwrap().verify().is_ok());
        assert!(bibliography.get_mut("cannonfodder").unwrap().verify().is_ok());

        let ill = bibliography.get("ill-defined").unwrap();
        let report = ill.verify();
        assert_eq!(report.missing.len(), 3);
        assert_eq!(report.superfluous.len(), 3);
        assert_eq!(report.malformed.len(), 1);
        assert!(report.missing.contains(&"title"));
        assert!(report.missing.contains(&"year"));
        assert!(report.missing.contains(&"editor"));
        assert!(report.superfluous.contains(&"maintitle"));
        assert!(report.superfluous.contains(&"author"));
        assert!(report.superfluous.contains(&"chapter"));
        assert_eq!(report.malformed[0].0.as_str(), "gender");
    }

    #[test]
    fn test_crossref() {
        let contents = fs::read_to_string("tests/cross.bib").unwrap();
        let bibliography = Bibliography::parse(&contents).unwrap();

        let e = bibliography.get("macmillan").unwrap();
        assert_eq!(e.publisher().unwrap()[0].format_verbatim(), "Macmillan");
        assert_eq!(e.location().unwrap().format_verbatim(), "New York and London");

        let book = bibliography.get("recursive").unwrap();
        assert_eq!(book.publisher().unwrap()[0].format_verbatim(), "Macmillan");
        assert_eq!(book.location().unwrap().format_verbatim(), "New York and London");
        assert_eq!(
            book.title().unwrap().format_verbatim(),
            "Recursive shennenigans and other important stuff"
        );

        assert_eq!(
            bibliography.get("arrgh").unwrap().parents().unwrap(),
            vec!["polecon".to_string()]
        );
        let arrgh = bibliography.get("arrgh").unwrap();
        assert_eq!(arrgh.entry_type, EntryType::Article);
        assert_eq!(arrgh.volume().unwrap(), PermissiveType::Typed(115));
        assert_eq!(arrgh.editors().unwrap()[0].0[0].name, "Uhlig");
        assert_eq!(arrgh.number().unwrap().format_verbatim(), "6");
        assert_eq!(
            arrgh.journal().unwrap().format_verbatim(),
            "Journal of Political Economy"
        );
        assert_eq!(
            arrgh.title().unwrap().format_verbatim(),
            "An‐arrgh‐chy: The Law and Economics of Pirate Organization"
        );
    }

    fn dump_debug(file: &str) {
        let contents = fs::read_to_string(file).unwrap();
        let bibliography = Bibliography::parse(&contents).unwrap();
        println!("{:#?}", bibliography);
    }

    fn dump_author_title(file: &str) {
        let contents = fs::read_to_string(file).unwrap();
        let bibliography = Bibliography::parse(&contents).unwrap();

        println!("{}", bibliography.to_biblatex_string());

        for x in bibliography {
            let authors = x.author().unwrap_or_default();
            for a in authors {
                print!("{}, ", a);
            }
            println!("\"{}\".", x.title().unwrap().format_sentence());
        }
    }

    #[test]
    fn linebreak_field() {
        let contents = r#"@book{key, title = {Hello
Martin}}"#;
        let bibliography = Bibliography::parse(contents).unwrap();
        let entry = bibliography.get("key").unwrap();
        assert_eq!(entry.title().unwrap().format_verbatim(), "Hello Martin");
    }

    #[test]
    fn test_verbatim_fields() {
        let contents = fs::read_to_string("tests/libra.bib").unwrap();
        let bibliography = Bibliography::parse(&contents).unwrap();

        // Import an entry/field with escaped colons
        let e = bibliography.get("dierksmeierJustHODLMoral2018").unwrap();
        assert_eq!(e.doi().unwrap(), "10.1007/s41463-018-0036-z");
        assert_eq!(
            e.file().unwrap(),
            "C:\\Users\\mhaug\\Zotero\\storage\\DTPR7TES\\Dierksmeier - 2018 - Just HODL On the Moral Claims of Bitcoin and Ripp.pdf"
        );

        // Import an entry/field with unescaped colons
        let e = bibliography.get("LibraAssociationIndependent").unwrap();
        assert_eq!(e.url().unwrap(), "https://libra.org/association/");

        // Test export of entry (not escaping colons)
        let e = bibliography.get("finextraFedGovernorChallenges2019").unwrap();
        assert_eq!(
            e.to_biblatex_string(),
            "@online{finextraFedGovernorChallenges2019,\nauthor = {FinExtra},\ndate = {2019-12-18},\nfile = {C:\\\\Users\\\\mhaug\\\\Zotero\\\\storage\\\\VY9LAKFE\\\\fed-governor-challenges-facebooks-libra-project.html},\ntitle = {Fed {Governor} Challenges {Facebook}'s {Libra} Project},\nurl = {https://www.finextra.com/newsarticle/34986/fed-governor-challenges-facebooks-libra-project},\nurldate = {2020-08-22},\n}"
        )
    }

    #[test]
    fn test_synthesized_entry() {
        let mut e = Entry::new("Test123".to_owned(), EntryType::Article);
        let brian = vec![Person {
            name: "Monroe".to_string(),
            given_name: "Brian Albert".to_string(),
            prefix: "".to_string(),
            suffix: "".to_string(),
        }];

        e.set_author(brian.clone());

        assert_eq!(Ok(brian), e.author());
    }

    #[test]
    fn test_case_sensitivity() {
        let contents = fs::read_to_string("tests/case.bib").unwrap();
        let bibliography = Bibliography::parse(&contents).unwrap();

        let entry = bibliography.get("biblatex2023").unwrap();
        let author = entry.author();

        match author {
            Ok(a) => assert_eq!(a[0].name, "Kime"),
            Err(RetrievalError::Missing(_)) => {
                panic!("Tags should be case insensitive.");
            }
            _ => panic!(),
        }
    }

    #[test]
    fn test_whitespace_collapse() {
        let raw = r#"@article{aksin,
            title        = {Effect of immobilization on catalytic characteristics of
                            saturated {Pd-N}-heterocyclic carbenes in {Mizoroki-Heck}
                            reactions},
          }"#;

        let bibliography = Bibliography::parse(raw).unwrap();
        let entry = bibliography.get("aksin").unwrap();
        assert_eq!(
            entry.title().unwrap().first().map(|s| s.as_ref().v),
            Some(Chunk::Normal(
                "Effect of immobilization on catalytic characteristics of saturated "
                    .to_string()
            ))
            .as_ref()
        );
    }

    #[test]
    fn test_empty_date_fields() {
        let raw = r#"@article{test,
            year        = 2000,
            day         = {},
            month    = {},
          }"#;

        let bibliography = Bibliography::parse(raw).unwrap();
        assert_eq!(
            bibliography.get("test").unwrap().date(),
            Err(TypeError::new(74..74, TypeErrorKind::MissingNumber).into())
        );
    }

    #[test]
    #[allow(clippy::single_range_in_vec_init)]
    fn test_page_ranges() {
        let raw = r#"@article{test,
            pages = {1---2},
          }
          @article{test1,
            pages = {2--3},
          }
          @article{test2,
            pages = {1},
          }"#;

        let bibliography = Bibliography::parse(raw).unwrap();
        assert_eq!(
            bibliography.get("test").unwrap().pages(),
            Ok(PermissiveType::Typed(vec![1..2]))
        );
        assert_eq!(
            bibliography.get("test1").unwrap().pages(),
            Ok(PermissiveType::Typed(vec![2..3]))
        );
        assert_eq!(
            bibliography.get("test2").unwrap().pages(),
            Ok(PermissiveType::Typed(vec![1..1]))
        );
    }
}
