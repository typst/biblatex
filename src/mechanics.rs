//! Defines the different bibliographical items and which fields should be
//! attached to each of them.

use std::str::FromStr;

use strum::{Display, EnumString};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Describes the type of a bibliographical entry.
///
/// Each type comes with a different set of required and allowable fields that
/// are taken into consideration in [`Entry::verify`](crate::Entry::verify).
#[derive(Debug, Clone, Eq, PartialEq, Display, EnumString)]
#[allow(missing_docs)]
#[strum(serialize_all = "lowercase")]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum EntryType {
    // BibTeX
    Article,
    Book,
    Booklet,
    InBook,
    InCollection,
    InProceedings,
    Manual,
    MastersThesis,
    PhdThesis,
    Misc,
    Proceedings,
    TechReport,
    Unpublished,

    // BibLaTeX
    MvBook,
    BookInBook,
    SuppBook,
    Periodical,
    SuppPeriodical,
    Collection,
    MvCollection,
    SuppCollection,
    Reference,
    MvReference,
    InReference,
    MvProceedings,
    Report,
    Patent,
    Thesis,
    Online,
    Software,
    Dataset,
    Set,
    XData,

    Unknown(String),
}

/// Describes the optionality mode of the `author` and `editor` fields.
#[derive(Clone, Debug, Default)]
pub enum AuthorMode {
    /// Neither of the fields are required to be set.
    NoneRequired,
    /// At least one of the fields must be present.
    OneRequired,
    /// Both fields must be set.
    BothRequired,
    /// The `author` field must be present.
    #[default]
    AuthorRequired,
    /// The `author` field must be present, the `editor` field is optional.
    AuthorRequiredEditorOptional,
    /// The `editor` field must be set while the `author` field must not be set.
    EditorRequiredAuthorForbidden,
}

impl AuthorMode {
    pub(crate) fn possible(&self) -> &'static [&'static str] {
        match self {
            Self::OneRequired
            | Self::BothRequired
            | Self::AuthorRequiredEditorOptional => &["author", "editor"],
            Self::AuthorRequired => &["author"],
            Self::EditorRequiredAuthorForbidden => &["editor"],
            _ => &[],
        }
    }
}

/// Describes the optionality mode of the `pages` and `chapter` field
#[derive(Clone, Debug, Default)]
pub enum PagesChapterMode {
    /// No specification for the `page` and `chapter` field is given.
    #[default]
    None,
    /// At least one of the fields must be present.
    OneRequired,
    /// Both fields are optional.
    BothOptional,
    /// Neither field may appear.
    BothForbidden,
    /// The `pages` field might be present, there is no specification for the
    /// `chapter` field.
    PagesOptional,
    /// The `pages` field must be present.
    #[allow(dead_code)]
    PagesRequired,
}

impl PagesChapterMode {
    pub(crate) fn possible(&self) -> &'static [&'static str] {
        match self {
            Self::OneRequired | Self::BothOptional => &["pages", "chapter"],
            Self::PagesOptional | Self::PagesRequired => &["pages"],
            _ => &[],
        }
    }
}

/// Specifies what kinds of fields an entry might have to hold.
#[derive(Debug, Default, Clone)]
pub struct Requirements {
    /// Fields that have to be present for the entry to be valid.
    pub required: Vec<&'static str>,
    /// Fields that might be present and are often used by bibliography styles.
    ///
    /// These fields, together with the required fields, will be taken into
    /// consideration for `crossref` and `xdata` transfers.
    pub optional: Vec<&'static str>,
    /// These fields must not appear for the entry to be valid.
    pub forbidden: Vec<&'static str>,
    /// Specifies the relation of author and editor field compulsiveness.
    pub author_eds_field: AuthorMode,
    /// Specifies the relation of page and chapter field compulsiveness.
    pub page_chapter_field: PagesChapterMode,
    /// Shows whether a `date` or `year` field has to be present.
    pub needs_date: bool,
}

impl EntryType {
    /// Parse from a string.
    ///
    /// Use this instead of the basic `from_str` when constructing from `.bib`
    /// files because case and aliases are considered here.
    pub fn new(name: &str) -> Self {
        let name = name.to_lowercase();

        if let Ok(ty) = EntryType::from_str(&name) {
            return ty;
        }

        match name.as_str() {
            "conference" => EntryType::InProceedings,
            "electronic" => EntryType::Online,
            "www" => EntryType::Online,
            _ => EntryType::Unknown(name),
        }
    }

    /// Is this a multi-volume work?
    pub fn is_multi_volume(&self) -> bool {
        matches!(
            self,
            Self::MvBook | Self::MvCollection | Self::MvReference | Self::MvProceedings
        )
    }

    /// Is this a single-volume composite work?
    pub fn is_collection(&self) -> bool {
        matches!(
            self,
            Self::Book
                | Self::Collection
                | Self::Periodical
                | Self::Reference
                | Self::Proceedings
        )
    }

    /// Convert into a type native to BibLaTeX.
    pub fn to_biblatex(&self) -> Self {
        match self {
            Self::MastersThesis => Self::Thesis,
            Self::PhdThesis => Self::Thesis,
            Self::TechReport => Self::Report,
            Self::Unknown(_) => Self::Misc,
            _ => self.clone(),
        }
    }

    /// Convert into a type supported by BibTeX.
    pub fn to_bibtex(&self) -> Self {
        match self {
            Self::MvBook => Self::Book,
            Self::BookInBook => Self::InBook,
            Self::SuppBook => Self::InBook,
            Self::Periodical => Self::Misc,
            Self::SuppPeriodical => Self::Article,
            Self::Collection => Self::Proceedings,
            Self::MvCollection => Self::Proceedings,
            Self::SuppCollection => Self::InCollection,
            Self::Reference => Self::Misc,
            Self::MvReference => Self::Misc,
            Self::InReference => Self::InCollection,
            Self::MvProceedings => Self::Proceedings,
            Self::Report => Self::TechReport,
            Self::Patent => Self::Misc,
            Self::Thesis => Self::PhdThesis,
            Self::Online => Self::Misc,
            Self::Software => Self::Misc,
            Self::Dataset => Self::Misc,
            Self::Set => Self::Misc,
            Self::XData => Self::Misc,
            Self::Unknown(_) => Self::Misc,
            _ => self.clone(),
        }
    }

    /// Get the required fields for the `EntryType`.
    pub(crate) fn requirements(&self) -> Requirements {
        let mut reqs = Requirements { needs_date: true, ..Default::default() };

        reqs.required.push("title");

        reqs.optional.push("note");
        reqs.optional.push("location");
        reqs.optional.push("titleadddon");
        reqs.optional.push("subtitle");
        reqs.optional.push("url");
        reqs.optional.push("urldate");
        reqs.optional.push("doi");
        reqs.optional.push("eprint");
        reqs.optional.push("eprintclass");
        reqs.optional.push("eprinttype");
        reqs.optional.push("pubstate");
        reqs.optional.push("language");
        reqs.optional.push("addendum");

        if self.is_multi_volume() {
            reqs.forbidden.push("maintitle");
            reqs.forbidden.push("mainsubtitle");
            reqs.forbidden.push("maintitleaddon");
            reqs.forbidden.push("part");
            reqs.forbidden.push("volume");
        }

        match self {
            Self::Article => {
                reqs.required.push("journaltitle");

                reqs.optional.remove(1);
                reqs.optional.push("number");
                reqs.optional.push("series");
                reqs.optional.push("version");
                reqs.optional.push("volume");
                reqs.optional.push("annotator");
                reqs.optional.push("commentator");
                reqs.optional.push("translator");
                reqs.optional.push("origlanguage");
                reqs.optional.push("journalsubtitle");
                reqs.optional.push("issue");
                reqs.optional.push("issuetitle");
                reqs.optional.push("issuesubtitle");
                reqs.optional.push("eid");
                reqs.optional.push("issn");

                reqs.page_chapter_field = PagesChapterMode::PagesOptional;
                reqs.author_eds_field = AuthorMode::AuthorRequiredEditorOptional;
            }
            Self::Book => {
                reqs.required.push("publisher");

                reqs.optional.push("edition");
                reqs.optional.push("number");
                reqs.optional.push("series");
                reqs.optional.push("part");
                reqs.optional.push("volume");
                reqs.optional.push("volumes");
                reqs.optional.push("annotator");
                reqs.optional.push("commentator");
                reqs.optional.push("translator");
                reqs.optional.push("origlanguage");
                reqs.optional.push("afterword");
                reqs.optional.push("foreword");
                reqs.optional.push("introduction");
                reqs.optional.push("maintitle");
                reqs.optional.push("mainsubtitle");
                reqs.optional.push("maintitleaddon");
                reqs.optional.push("isbn");
                reqs.optional.push("pagetotal");

                reqs.author_eds_field = AuthorMode::OneRequired;
                reqs.page_chapter_field = PagesChapterMode::BothOptional;
            }
            Self::Booklet => {
                reqs.optional.push("howpublished");
                reqs.optional.push("type");
                reqs.optional.push("pagetotal");

                reqs.author_eds_field = AuthorMode::OneRequired;
                reqs.page_chapter_field = PagesChapterMode::BothOptional;
                reqs.needs_date = false;
            }
            Self::InBook => {
                reqs.required.push("publisher");
                reqs.required.push("booktitle");

                reqs.optional.push("bookauthor");
                reqs.optional.push("volume");
                reqs.optional.push("volumes");
                reqs.optional.push("part");
                reqs.optional.push("type");
                reqs.optional.push("series");
                reqs.optional.push("number");
                reqs.optional.push("edition");
                reqs.optional.push("annotator");
                reqs.optional.push("commentator");
                reqs.optional.push("translator");
                reqs.optional.push("origlanguage");
                reqs.optional.push("afterword");
                reqs.optional.push("foreword");
                reqs.optional.push("introduction");
                reqs.optional.push("maintitle");
                reqs.optional.push("mainsubtitle");
                reqs.optional.push("maintitleaddon");
                reqs.optional.push("booksubtitle");
                reqs.optional.push("booktitleaddon");
                reqs.optional.push("isbn");

                reqs.forbidden.push("pagetotal");

                reqs.author_eds_field = AuthorMode::OneRequired;
                reqs.page_chapter_field = PagesChapterMode::OneRequired;
            }
            Self::InCollection => {
                reqs.required.push("publisher");
                reqs.required.push("booktitle");

                reqs.optional.push("volume");
                reqs.optional.push("type");
                reqs.optional.push("series");
                reqs.optional.push("number");
                reqs.optional.push("edition");
                reqs.optional.push("annotator");
                reqs.optional.push("commentator");
                reqs.optional.push("translator");
                reqs.optional.push("origlanguage");
                reqs.optional.push("afterword");
                reqs.optional.push("foreword");
                reqs.optional.push("introduction");
                reqs.optional.push("maintitle");
                reqs.optional.push("mainsubtitle");
                reqs.optional.push("maintitleaddon");
                reqs.optional.push("booksubtitle");
                reqs.optional.push("booktitleaddon");
                reqs.optional.push("part");
                reqs.optional.push("volumes");
                reqs.optional.push("isbn");

                reqs.forbidden.push("pagetotal");

                reqs.author_eds_field = AuthorMode::BothRequired;
                reqs.page_chapter_field = PagesChapterMode::BothOptional;
            }
            Self::InProceedings => {
                reqs.required.push("booktitle");

                reqs.optional.push("number");
                reqs.optional.push("organization");
                reqs.optional.push("series");
                reqs.optional.push("volume");
                reqs.optional.push("volumes");
                reqs.optional.push("part");
                reqs.optional.push("publisher");
                reqs.optional.push("maintitle");
                reqs.optional.push("mainsubtitle");
                reqs.optional.push("maintitleaddon");
                reqs.optional.push("booksubtitle");
                reqs.optional.push("booktitleaddon");
                reqs.optional.push("eventtitle");
                reqs.optional.push("eventsubtitle");
                reqs.optional.push("eventtitleaddon");
                reqs.optional.push("venue");
                reqs.optional.push("isbn");
                reqs.optional.push("publisher");

                reqs.forbidden.push("pagetotal");

                reqs.page_chapter_field = PagesChapterMode::BothOptional;
                reqs.author_eds_field = AuthorMode::AuthorRequiredEditorOptional;
            }
            Self::Manual => {
                reqs.optional.push("edition");
                reqs.optional.push("organization");
                reqs.optional.push("series");
                reqs.optional.push("version");
                reqs.optional.push("isbn");
                reqs.optional.push("publisher");
                reqs.optional.push("type");
                reqs.optional.push("pagetotal");

                reqs.author_eds_field = AuthorMode::OneRequired;
                reqs.page_chapter_field = PagesChapterMode::BothOptional;
                reqs.needs_date = false;
            }
            Self::MastersThesis => {
                reqs.required.push("school");

                reqs.optional.push("type");
                reqs.author_eds_field = AuthorMode::AuthorRequired;
            }
            Self::Misc => {
                reqs.optional.remove(1);
                reqs.optional.push("howpublished");
                reqs.optional.push("organization");
                reqs.optional.push("type");

                reqs.author_eds_field = AuthorMode::OneRequired;
                // reqs.page_chapter_field = PagesChapterMode::BothOptional;
                reqs.needs_date = false;
            }
            Self::Proceedings => {
                reqs.optional.push("number");
                reqs.optional.push("organization");
                reqs.optional.push("series");
                reqs.optional.push("volume");
                reqs.optional.push("volumes");
                reqs.optional.push("part");
                reqs.optional.push("publisher");
                reqs.optional.push("maintitle");
                reqs.optional.push("mainsubtitle");
                reqs.optional.push("maintitleaddon");
                reqs.optional.push("isbn");
                reqs.optional.push("publisher");
                reqs.optional.push("pagetotal");

                reqs.author_eds_field = AuthorMode::EditorRequiredAuthorForbidden;
                reqs.page_chapter_field = PagesChapterMode::BothOptional;
            }
            Self::TechReport => {
                reqs.required.push("institution");

                reqs.optional.push("number");
                reqs.optional.push("type");
            }
            Self::Unpublished => {
                reqs.required.push("note");

                reqs.optional.remove(1);
                reqs.optional.remove(0);
                reqs.optional.push("isbn");
                reqs.optional.push("howpublished");

                reqs.needs_date = false;
            }
            Self::MvBook => {
                reqs.optional.push("annotator");
                reqs.optional.push("commentator");
                reqs.optional.push("translator");
                reqs.optional.push("origlanguage");
                reqs.optional.push("afterword");
                reqs.optional.push("foreword");
                reqs.optional.push("introduction");
                reqs.optional.push("edition");
                reqs.optional.push("number");
                reqs.optional.push("series");
                reqs.optional.push("volumes");
                reqs.optional.push("isbn");
                reqs.optional.push("publisher");
                reqs.optional.push("pagetotal");

                reqs.page_chapter_field = PagesChapterMode::BothOptional;
                reqs.author_eds_field = AuthorMode::AuthorRequiredEditorOptional;
            }
            Self::Periodical => {
                reqs.optional.push("issue");
                reqs.optional.push("issuetitle");
                reqs.optional.push("issuesubtitle");
                reqs.optional.push("number");
                reqs.optional.push("series");
                reqs.optional.push("volume");
                reqs.optional.push("issn");

                reqs.author_eds_field = AuthorMode::EditorRequiredAuthorForbidden;
            }
            Self::Collection => {
                reqs.optional.push("annotator");
                reqs.optional.push("commentator");
                reqs.optional.push("translator");
                reqs.optional.push("origlanguage");
                reqs.optional.push("afterword");
                reqs.optional.push("foreword");
                reqs.optional.push("introduction");
                reqs.optional.push("maintitle");
                reqs.optional.push("mainsubtitle");
                reqs.optional.push("maintitleaddon");
                reqs.optional.push("edition");
                reqs.optional.push("number");
                reqs.optional.push("series");
                reqs.optional.push("part");
                reqs.optional.push("volume");
                reqs.optional.push("volumes");
                reqs.optional.push("isbn");
                reqs.optional.push("publisher");
                reqs.optional.push("pagetotal");

                reqs.author_eds_field = AuthorMode::EditorRequiredAuthorForbidden;
                reqs.page_chapter_field = PagesChapterMode::BothOptional;
            }
            Self::MvCollection => {
                reqs.optional.push("annotator");
                reqs.optional.push("commentator");
                reqs.optional.push("translator");
                reqs.optional.push("origlanguage");
                reqs.optional.push("afterword");
                reqs.optional.push("foreword");
                reqs.optional.push("introduction");
                reqs.optional.push("edition");
                reqs.optional.push("number");
                reqs.optional.push("series");
                reqs.optional.push("volumes");
                reqs.optional.push("isbn");
                reqs.optional.push("publisher");
                reqs.optional.push("pagetotal");

                reqs.author_eds_field = AuthorMode::EditorRequiredAuthorForbidden;
                reqs.page_chapter_field = PagesChapterMode::BothForbidden;
            }
            Self::MvProceedings => {
                reqs.optional.push("number");
                reqs.optional.push("series");
                reqs.optional.push("volumes");
                reqs.optional.push("publisher");
                reqs.optional.push("organization");
                reqs.optional.push("pagetotal");

                reqs.author_eds_field = AuthorMode::EditorRequiredAuthorForbidden;
                reqs.page_chapter_field = PagesChapterMode::BothForbidden;
            }
            Self::Report => {
                reqs.required.push("institution");
                reqs.required.push("type");

                reqs.optional.push("number");
                reqs.optional.push("version");
                reqs.optional.push("isrn");
                reqs.optional.push("pagetotal");

                reqs.page_chapter_field = PagesChapterMode::BothOptional;
            }
            Self::Patent => {
                reqs.required.push("number");

                reqs.optional.push("holder");
                reqs.optional.push("type");
            }
            Self::Thesis => {
                reqs.optional.push("isbn");
                reqs.required.push("institution");
                reqs.required.push("type");
                reqs.optional.push("pagetotal");

                reqs.page_chapter_field = PagesChapterMode::BothOptional;
            }
            Self::Online => {
                reqs.required.push("url");

                reqs.optional.remove(9);
                reqs.optional.remove(8);
                reqs.optional.remove(7);
                reqs.optional.remove(6);
                reqs.optional.remove(4);
                reqs.optional.remove(1);
                reqs.optional.push("organization");

                reqs.author_eds_field = AuthorMode::OneRequired;
            }
            Self::Dataset => {
                reqs.optional.push("edition");
                reqs.optional.push("type");
                reqs.optional.push("series");
                reqs.optional.push("number");
                reqs.optional.push("version");
                reqs.optional.push("organization");
                reqs.optional.push("publisher");

                reqs.author_eds_field = AuthorMode::OneRequired;
            }
            Self::PhdThesis => {
                reqs = Self::MastersThesis.requirements();
            }
            Self::SuppPeriodical => {
                reqs = Self::Article.requirements();
            }
            Self::BookInBook => {
                reqs = Self::InBook.requirements();
            }
            Self::SuppBook => {
                reqs = Self::InBook.requirements();
            }
            Self::SuppCollection => {
                reqs = Self::InCollection.requirements();
            }
            Self::Reference => {
                reqs = Self::Collection.requirements();
            }
            Self::MvReference => {
                reqs = Self::MvCollection.requirements();
            }
            Self::InReference => {
                reqs = Self::InCollection.requirements();
            }
            Self::Software => {
                reqs = Self::Misc.requirements();
            }
            Self::Set => {
                reqs.optional.clear();
                reqs.required = vec!["entryset"];
                reqs.author_eds_field = AuthorMode::NoneRequired;
                reqs.needs_date = false;
            }
            Self::XData => {
                reqs.optional.clear();
                reqs.required.clear();
                reqs.author_eds_field = AuthorMode::NoneRequired;
                reqs.needs_date = false;
            }
            Self::Unknown(_) => {
                reqs = Self::MvCollection.requirements();
            }
        }

        reqs
    }
}

/// Whether a field with this key should be parsed with commands and most
/// escapes turned off.
pub fn is_verbatim_field(key: &str) -> bool {
    matches!(
        key,
        "file"
            | "doi"
            | "uri"
            | "eprint"
            | "verba"
            | "verbb"
            | "verbc"
            | "pdf"
            | "url"
            | "urlraw"
    )
}
