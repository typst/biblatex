mod chunk;
mod mechanics;
mod raw;
mod resolve;
mod types;

pub use chunk::*;
pub use mechanics::*;
pub use raw::*;
pub use types::*;

use std::collections::HashMap;
use std::fmt::Write as WriteFmt;
use std::io::{self, Write};

use paste::paste;

/// A fully parsed bibliography.
#[derive(Debug, Clone)]
pub struct Bibliography {
    /// The bibliography entries.
    entries: Vec<Entry>,
    /// Maps from citation keys to indices in `items`.
    keys: HashMap<String, usize>,
}

/// A bibliography entry containing chunk fields, which can be parsed into more
/// specific types on demand.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Entry {
    /// The citation key.
    pub key: String,
    /// Denotes the type of bibliography item (e.g. `article`).
    pub entry_type: EntryType,
    /// Maps from field names to their associated chunk vectors.
    pub fields: HashMap<String, Chunks>,
}

impl Bibliography {
    /// Create a new, empty bibliography.
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            keys: HashMap::new(),
        }
    }

    /// Parse a bibliography from a source string.
    pub fn parse(src: &str) -> Self {
        Self::from_raw(RawBibliography::parse(src))
    }

    /// Construct a bibliography from a raw bibliography.
    pub fn from_raw(raw: RawBibliography) -> Self {
        let mut res = Self::new();
        let abbreviations = &raw.abbreviations;

        for entry in raw.entries {
            res.insert(Entry {
                key: entry.key.to_string(),
                entry_type: EntryType::robust_from_str(entry.entry_type),
                fields: entry
                    .fields
                    .into_iter()
                    .map(|(key, value)| {
                        (key.to_string(), resolve::resolve(value, abbreviations))
                    })
                    .collect(),
            });
        }

        res
    }

    /// The number of bibliography entries.
    pub fn len(&self) -> usize {
        self.entries.len()
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

    /// Try to find an entry with the given cite key and return a copy of that
    /// entry with all `crossref` and `xdata` dependencies resolved.
    pub fn get_resolved(&self, key: &str) -> Option<Entry> {
        let mut entry = self.get(key)?.clone();
        entry.resolve_crossrefs(self);
        Some(entry)
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
            if let Some(ids) = entry.get_as::<Vec<String>>("ids") {
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

    /// Serialize this bibliography into a BibLaTeX string.
    pub fn to_biblatex_string(&mut self) -> String {
        let mut biblatex = String::new();
        for entry in self.entries.iter_mut() {
            biblatex.push_str(&entry.to_biblatex_string());
            biblatex.push('\n');
        }
        biblatex
    }

    /// Write the entry into a writer in the BibLaTeX format.
    pub fn write_biblatex(&mut self, mut sink: impl Write) -> io::Result<()> {
        for entry in self.entries.iter_mut() {
            writeln!(sink, "{}", entry.to_biblatex_string())?;
        }
        Ok(())
    }

    /// An iterator over the bibliography's entries.
    pub fn iter(&self) -> std::slice::Iter<Entry> {
        self.entries.iter()
    }

    /// A mutable iterator over the bibliography's entries.
    pub fn iter_mut(&mut self) -> std::slice::IterMut<Entry> {
        self.entries.iter_mut()
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
        Self { key, entry_type, fields: HashMap::new() }
    }

    /// Get the chunk slice for a field.
    ///
    /// The field key must be lowercase.
    pub fn get(&self, key: &str) -> Option<&[Chunk]> {
        self.fields.get(key).map(AsRef::as_ref)
    }

    /// Parse the chunk slice for a field as a specific type.
    pub fn get_as<T: Type>(&self, key: &str) -> Option<T> {
        self.get(key)?.parse::<T>()
    }

    /// Get an entry but return None for empty chunk slices.
    fn get_non_empty(&self, key: &str) -> Option<&[Chunk]> {
        let entry = self.get(key)?;
        if !entry.is_empty() { Some(entry) } else { None }
    }

    /// Sets a field value as a chunk vector.
    pub fn set(&mut self, key: &str, chunks: Chunks) {
        self.fields.insert(key.to_lowercase(), chunks);
    }

    /// Sets a field value as a chunk vector as a specific type.
    pub fn set_as<T: Type>(&mut self, key: &str, value: &T) {
        self.set(key, value.to_chunks());
    }

    /// Removes a field from the entry.
    pub fn remove(&mut self, key: &str) -> Option<Chunks> {
        self.fields.remove(key)
    }

    /// Serialize this entry into a BibLaTeX string.
    pub fn to_biblatex_string(&mut self) -> String {
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

            writeln!(biblatex, "{} = {},", key, value.to_biblatex_string()).unwrap();
        }

        biblatex.push('}');
        biblatex
    }

    /// Serialize this entry into a BibTeX string.
    pub fn to_bibtex_string(&mut self) -> String {
        let mut bibtex = String::new();
        let ty = self.entry_type.to_bibtex();
        let thesis = matches!(ty, EntryType::PhdThesis | EntryType::MastersThesis);

        writeln!(bibtex, "@{}{{{},", ty, self.key).unwrap();

        for (key, value) in &self.fields {
            if key == "date" {
                if let Some(date) = self.date() {
                    for (key, value) in date.to_fieldset() {
                        let v = [Chunk::Normal(value)].to_biblatex_string();
                        writeln!(bibtex, "{} = {},", key, v).unwrap();
                    }
                }
                continue;
            }

            let key = match key.as_ref() {
                "journaltitle" => "journal",
                "location" => "address",
                "institution" if thesis => "school",
                k => k,
            };

            writeln!(bibtex, "{} = {},", key, value.to_biblatex_string()).unwrap();
        }

        bibtex.push('}');
        bibtex
    }

    /// The parents of an entry in a semantic sense (`crossref` and `xref`).
    pub fn parents(&self) -> Vec<String> {
        let mut parents = vec![];

        if let Some(crossref) = self.get_as::<String>("crossref") {
            parents.push(crossref);
        }

        if let Some(xrefs) = self.get_as::<Vec<String>>("xref") {
            parents.extend(xrefs);
        }

        parents
    }

    /// Resolve data dependencies using another entry.
    fn resolve_single_crossref(&mut self, crossref: Entry) {
        let typ = self.entry_type.clone();
        let mut requirements = typ.get_requirements();
        let mut active_fields = requirements.required.clone();
        active_fields.append(&mut requirements.optional);
        active_fields.append(&mut requirements.page_chapter_field.get_all_possible());
        active_fields.append(&mut requirements.author_eds_field.get_all_possible());

        if self.entry_type == EntryType::XData {
            for f in crossref.fields.keys() {
                active_fields.push(f);
            }
        }

        for f in active_fields {
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
            return;
        }

        if requirements.needs_date {
            if let Some(date) = crossref.date() {
                self.set_date(date);
            }
        }
    }

    /// Resolves all data dependancies defined by `crossref` and `xdata` fields.
    fn resolve_crossrefs(&mut self, bib: &Bibliography) {
        let mut refs = vec![];

        if let Some(crossref) = self.get_as::<String>("crossref") {
            refs.extend(bib.get(&crossref).cloned());
        }

        if let Some(keys) = self.get_as::<Vec<String>>("xdata") {
            for key in keys {
                refs.extend(bib.get(&key).cloned());
            }
        }

        for mut crossref in refs {
            crossref.resolve_crossrefs(bib);
            self.resolve_single_crossref(crossref);
        }

        self.remove("crossref");
        self.remove("xdata");
    }

    /// Verify if the entry has all fields required for its [`EntryType`].
    ///
    /// This function returns `Ok(())` upon successful validation. The `Err`
    /// variant of the result contains a pair carrying two vectors of keys: The
    /// first indicating fields that should have been present but were not, the
    /// second indicating fields that were set but are forbidden by the
    /// [`EntryType`].
    ///
    /// _Note:_ This function will not resolve the entry. If you want to support
    /// / expect files using `crossref` and `xdata`, you will want to call this
    /// method only on entries obtained through the `Bibliography::get_resolved`
    /// call.
    pub fn verify(&self) -> Result<(), (Vec<&str>, Vec<&str>)> {
        let reqs = self.entry_type.get_requirements();
        let mut expected = vec![];
        let mut outlawed = vec![];

        for field in reqs.required {
            match field {
                "journaltitle" => {
                    if self
                        .get_non_empty(field)
                        .or_else(|| self.get_non_empty("journal"))
                        .is_none()
                    {
                        expected.push(field);
                    }
                }
                "location" => {
                    if self
                        .get_non_empty(field)
                        .or_else(|| self.get_non_empty("address"))
                        .is_none()
                    {
                        expected.push(field);
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
                        expected.push(field);
                    }
                }
                _ => {
                    if self.get_non_empty(field).is_none() {
                        expected.push(field);
                    }
                }
            }
        }

        for field in reqs.forbidden {
            if self.get_non_empty(field).is_some() {
                outlawed.push(field);
            }
        }

        if reqs.needs_date {
            if self.date().is_none() {
                expected.push("year");
            }
        }

        match reqs.page_chapter_field {
            PagesChapterMode::PagesRequired => {
                if self.pages().is_none() {
                    expected.push("pages");
                }
            }
            PagesChapterMode::PagesChapterRequired => {
                if self.pages().is_none() && self.chapter().is_none() {
                    expected.push("pages");
                }
            }
            PagesChapterMode::BothForbidden => {
                if self.pages().is_some() {
                    outlawed.push("pages");
                }
                if self.chapter().is_some() {
                    outlawed.push("chapter");
                }
            }
            _ => {}
        }

        match reqs.author_eds_field {
            AuthorMode::AuthorRequired | AuthorMode::AuthorRequiredEditorOptional => {
                if self.author().is_none() {
                    expected.push("author");
                }
            }
            AuthorMode::AuthorEditorRequired => {
                if self.author().is_none() && self.editors().is_empty() {
                    expected.push("author");
                }
            }
            AuthorMode::EditorRequired => {
                if self.editors().is_empty() {
                    expected.push("editor");
                }
            }
            AuthorMode::EditorRequiredAuthorForbidden => {
                if self.editors().is_empty() {
                    expected.push("editor");
                }
                if self.author().is_some() {
                    outlawed.push("author");
                }
            }
            AuthorMode::BothRequired => {
                if self.editors().is_empty() {
                    expected.push("editor");
                }
                if self.author().is_none() {
                    expected.push("author");
                }
            }
            _ => {}
        }

        if expected.is_empty() && outlawed.is_empty() {
            Ok(())
        } else {
            Err((expected, outlawed))
        }
    }
}

macro_rules! fields {
    ($($name:ident: $field:expr $(=> $ret:ty)?),* $(,)*) => {
        $(paste! {
            #[doc = "Get the `" $field "` field."]
            pub fn $name(&self) -> Option<fields!(@ret $($ret)?)> {
                self.get($field)$(?.parse::<$ret>())?
            }

            fields!(@set $name => $field, $($ret)?);
        })*
    };

    (@ret) => {&[Chunk]};
    (@ret $ret:ty) => {$ret};

    (@set $name:ident => $field:literal, ) => {
        paste! {
            #[doc = "Set the value of the `" $field "` field."]
            pub fn [<set_ $name>](&mut self, item: Chunks) {
                self.set($field, item);
            }
        }
    };
    (@set $name:ident => $field:literal, $ty:ty) => {
        paste! {
            #[doc = "Set the value of the `" $field "` field."]
            pub fn [<set_ $name>](&mut self, item: $ty) {
                self.set($field, item.to_chunks());
            }
        }
    };
}

macro_rules! alias_fields {
    ($($name:ident: $field:literal | $alias:literal $(=> $ret:ty)?),* $(,)*) => {
        $(paste! {
            #[doc = "Get the `" $field "` field, falling back on `" $alias "`
                     if `" $field "` is empty."]
            pub fn $name(&self) -> Option<fields!(@ret $($ret)?)> {
                self.get($field)
                    .or_else(|| self.get($alias))
                    $(?.parse::<$ret>())?
            }

            fields!(@set $name => $field, $($ret)?);
        })*
    };
}

macro_rules! date_fields {
    ($($name:ident: $prefix:literal),* $(,)*) => {
        $(paste! {
            #[doc = "Get the `" $prefix "date` field, falling back on the
                     `" $prefix "year`, `" $prefix "month`, and
                     `" $prefix "day` fields if it is not present."]
            pub fn $name(&self) -> Option<Date> {
                if let Some(chunks) = self.get(concat!($prefix, "date")) {
                    chunks.parse::<Date>()
                } else {
                    Date::new_from_three_fields(
                        self.get(concat!($prefix, "year"))?,
                        self.get(concat!($prefix, "month")),
                        self.get(concat!($prefix, "day")),
                    )
                }
            }

            #[doc = "Set the value of the `" $prefix "date` field, removing the
                     `" $prefix "year`, `" $prefix "month`, and
                     `" $prefix "day` fields if present."]
            pub fn [<set_ $name>](&mut self, item: Date) {
                self.set(concat!($prefix, "date"), item.to_chunks());
                self.remove(concat!($prefix, "year"));
                self.remove(concat!($prefix, "month"));
                self.remove(concat!($prefix, "day"));
            }
        })*
    };
}

impl Entry {
    // BibTeX fields.
    fields! {
        // Fields without a specified return type simply return `&[Chunk]`.
        author: "author" => Vec<Person>,
        book_title: "booktitle",
        chapter: "chapter",
        edition: "edition" => IntOrChunks,
        how_published: "howpublished",
        note: "note",
        number: "number",
        organization: "organization" => Vec<Chunks>,
        pages: "pages" => Vec<std::ops::Range<u32>>,
        publisher: "publisher" => Vec<Chunks>,
        series: "series",
        title: "title",
        type_: "type" => String,
        volume: "volume" => i64,
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
    pub fn editors(&self) -> Vec<(Vec<Person>, EditorType)> {
        let mut editors = vec![];

        let mut parse = |name_field: &str, editor_field: &str| {
            if let Some(persons) = self.get_as::<Vec<Person>>(name_field) {
                let editor_type = self
                    .get(editor_field)
                    .and_then(|chunks| chunks.parse::<EditorType>())
                    .unwrap_or(EditorType::Editor);
                editors.push((persons, editor_type));
            }
        };

        parse("editor", "editortype");
        parse("editora", "editoratype");
        parse("editorb", "editorbtype");
        parse("editorc", "editorctype");

        editors
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

#[cfg(test)]
mod tests {
    use std::fs;

    use super::*;

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
    fn test_alias() {
        let contents = fs::read_to_string("tests/cross.bib").unwrap();
        let mut bibliography = Bibliography::parse(&contents);

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
        let mut bibliography = Bibliography::parse(&contents);

        let biblatex = bibliography.get_mut("haug2019").unwrap().to_biblatex_string();
        assert!(biblatex.contains("institution = {Technische Universität Berlin},"));

        let bibtex = bibliography.get_mut("haug2019").unwrap().to_bibtex_string();
        assert!(bibtex.contains("school = {Technische Universität Berlin},"));
        assert!(bibtex.contains("year = {2019},"));
        assert!(bibtex.contains("month = {10},"));
        assert!(!bibtex.contains("institution"));
        assert!(!bibtex.contains("date"));
    }

    #[test]
    fn test_verify() {
        let contents = fs::read_to_string("tests/cross.bib").unwrap();
        let mut bibliography = Bibliography::parse(&contents);

        assert!(bibliography.get_mut("haug2019").unwrap().verify().is_ok());
        assert!(bibliography.get_mut("cannonfodder").unwrap().verify().is_ok());

        let ill = bibliography.get("ill-defined").unwrap();
        if let Err((exp, forb)) = ill.verify() {
            assert!(exp.contains(&"title"));
            assert!(exp.contains(&"year"));
            assert!(exp.contains(&"editor"));
            assert!(forb.contains(&"maintitle"));
            assert!(forb.contains(&"author"));
            assert!(forb.contains(&"chapter"));
            assert_eq!(exp.len(), 3);
            assert_eq!(forb.len(), 3);
        } else {
            panic!("Should not have passed test");
        }
    }

    #[test]
    fn test_crossref() {
        let contents = fs::read_to_string("tests/cross.bib").unwrap();
        let bibliography = Bibliography::parse(&contents);

        let e = bibliography.get_resolved("macmillan").unwrap();
        assert_eq!(e.publisher().unwrap()[0].format_verbatim(), "Macmillan");
        assert_eq!(
            e.location().unwrap().format_verbatim(),
            "New York and London"
        );

        let book = bibliography.get_resolved("recursive").unwrap();
        assert_eq!(book.publisher().unwrap()[0].format_verbatim(), "Macmillan");
        assert_eq!(
            book.location().unwrap().format_verbatim(),
            "New York and London"
        );
        assert_eq!(
            book.title().unwrap().format_verbatim(),
            "Recursive shennenigans and other important stuff"
        );

        assert_eq!(bibliography.get("arrgh").unwrap().parents(), vec![
            "polecon".to_string()
        ]);
        let arrgh = bibliography.get_resolved("arrgh").unwrap();
        assert_eq!(arrgh.entry_type, EntryType::Article);
        assert_eq!(arrgh.volume().unwrap(), 115);
        assert_eq!(arrgh.editors()[0].0[0].name, "Uhlig");
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
        let bibliography = Bibliography::parse(&contents);
        println!("{:#?}", bibliography);
    }

    fn dump_author_title(file: &str) {
        let contents = fs::read_to_string(file).unwrap();
        let mut bibliography = Bibliography::parse(&contents);

        println!("{}", bibliography.to_biblatex_string());

        for x in bibliography {
            let authors = x.author().unwrap_or_default();
            for a in authors {
                print!("{}, ", a);
            }
            println!("\"{}\".", x.title().unwrap().format_sentence());
        }
    }
}
