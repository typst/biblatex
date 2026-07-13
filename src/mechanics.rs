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
///
/// References:
/// - BibTeX: [3.1 Entry Types — BibTeXing (`btxdoc.pdf`, 1988-02-08) | CTAN](https://mirrors.ctan.org/biblio/bibtex/base/btxdoc.pdf)
/// - BibLaTeX: [2.1 Entry Types — The `biblatex` Package (`biblatex.pdf`, v3.21, 2025-07-10) | CTAN](https://mirrors.ctan.org/macros/latex/contrib/biblatex/doc/biblatex.pdf#subsection.2.1)
#[derive(Debug, Clone, Eq, PartialEq, Display, EnumString)]
#[allow(missing_docs)]
#[strum(serialize_all = "lowercase")]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum EntryType {
    /// BibTeX: An article from a journal or magazine.
    ///
    /// BibLaTeX regular type: An article in a journal, magazine, newspaper, or other periodical which forms a self-contained unit with its own title.
    Article,
    /// BibTeX: A book with an explicit publisher.
    ///
    /// BibLaTeX regular type: A single-volume book with one or more authors where the authors share credit for the work as a whole. This entry type also covers the function of the [`@inbook`][Self::InBook] type of traditional BibTeX, see [§2.3.1 of `biblatex.pdf`][biblatex-2.3.1] for details.
    ///
    /// [biblatex-2.3.1]: https://mirrors.ctan.org/macros/latex/contrib/biblatex/doc/biblatex.pdf#subsubsection.2.3.1
    Book,
    /// BibTeX: A work that is printed and bound, but without a named publisher or sponsoring institution.
    ///
    /// BibLaTeX regular type: A book-like work without a formal publisher or sponsoring institution.
    Booklet,
    /// BibTeX: A part of a book, which may be a chapter (or section or whatever) and/or a range of pages.
    ///
    /// BibLaTeX regular type: A part of a book which forms a self-contained unit with its own title. Note that the profile of this entry type is different from standard BibTeX, see [§2.3.1 of `biblatex.pdf`][biblatex-2.3.1].
    ///
    /// [biblatex-2.3.1]: https://mirrors.ctan.org/macros/latex/contrib/biblatex/doc/biblatex.pdf#subsubsection.2.3.1
    InBook,
    /// BibTeX: A part of a book having its own title.
    ///
    /// BibLaTeX regular type: A contribution to a collection which forms a self-contained unit with a distinct author and title.
    InCollection,
    /// BibTeX: An article in a conference proceedings. `@conference` is the same as this type, included for _Scribe_ compatibility.
    ///
    /// BibLaTeX regular type: An article in a conference proceedings. This type is similar to [`@incollection`][Self::InCollection]. `@conference` is a legacy alias for this type.
    InProceedings,
    /// BibTeX: Technical documentation.
    ///
    /// BibLaTeX regular type: Technical or other documentation, not necessarily in printed form.
    Manual,
    /// BibTeX: A Master’s thesis.
    ///
    /// BibLaTeX type alias: Similar to [`@thesis`][Self::Thesis] except that the `type` field is optional and defaults to the localised term ‘Master’s thesis’.
    MastersThesis,
    /// BibTeX: A PhD thesis.
    ///
    /// BibLaTeX type alias: Similar to [`@thesis`][Self::Thesis] except that the `type` field is optional and defaults to the localised term ‘PhD thesis’.
    PhdThesis,
    /// BibTeX: Use this type when nothing else fits.
    ///
    /// BibLaTeX regular type: A fallback type for entries which do not fit into any other category.
    Misc,
    /// BibTeX: The proceedings of a conference.
    ///
    /// BibLaTeX regular type: A single-volume conference proceedings. This type is very similar to [`@collection`][Self::Collection].
    Proceedings,
    /// BibTeX: A report published by a school or other institution, usually numbered within a series.
    ///
    /// BibLaTeX type alias: Similar to [`@report`][Self::Report] except that the `type` field is optional and defaults to the localised term ‘technical report’.
    TechReport,
    /// BibTeX: A document having an author and title, but not formally published.
    ///
    /// BibLaTeX regular type: A work with an author and a title which has not been formally published, such as a manuscript or the script of a talk.
    Unpublished,

    /// BibLaTeX regular type: A multi-volume [`@book`][Self::Book]. For backwards compatibility, multi-volume books are also supported by the entry type [`@book`][Self::Book]. However, it is advisable to make use of the dedicated entry type `@mvbook`.
    MvBook,
    /// BibLaTeX regular type: This type is similar to [`@inbook`][Self::InBook] but intended for works originally published as a stand-alone book. A typical example are books reprinted in the collected works of an author.
    BookInBook,
    /// BibLaTeX regular type: Supplemental material in a [`@book`][Self::Book]. This type is closely related to the [`@inbook`][Self::InBook] entry type. While [`@inbook`][Self::InBook] is primarily intended for a part of a book with its own title (e. g., a single essay in a collection of essays by the same author), this type is provided for elements such as prefaces, introductions, forewords, afterwords, etc. which often have a generic title only. Style guides may require such items to be formatted differently from other [`@inbook`][Self::InBook] items. The standard styles will treat this entry type as an alias for [`@inbook`][Self::InBook].
    SuppBook,
    /// BibLaTeX regular type: An complete issue of a periodical, such as a special issue of a journal.
    Periodical,
    /// BibLaTeX regular type: Supplemental material in a [`@periodical`][Self::Periodical]. This type is similar to [`@suppbook`][Self::SuppBook] but related to the [`@periodical`][Self::Periodical] entry type. The role of this entry type may be more obvious if you bear in mind that the [`@article`][Self::Article] type could also be called `@inperiodical`. This type may be useful when referring to items such as regular columns, obituaries, letters to the editor, etc. which only have a generic title. Style guides may require such items to be formatted differently from articles in the strict sense of the word. The standard styles will treat this entry type as an alias for [`@article`][Self::Article].
    SuppPeriodical,
    /// BibLaTeX regular type: A single-volume collection with multiple, self-contained contributions by distinct authors which have their own title. The work as a whole has no overall author but it will usually have an editor.
    Collection,
    /// BibLaTeX regular type: A multi-volume [`@collection`][Self::Collection]. For backwards compatibility, multi-volume collections are also supported by the entry type [`@collection`][Self::Collection]. However, it is advisable to make use of the dedicated entry type `@mvcollection`.
    MvCollection,
    /// BibLaTeX regular type: Supplemental material in a [`@collection`][Self::Collection]. This type is similar to [`@suppbook`][Self::SuppBook] but related to the [`@collection`][Self::Collection] entry type. The standard styles will treat this entry type as an alias for [`@incollection`][Self::InCollection].
    SuppCollection,
    /// BibLaTeX regular type: A single-volume work of reference such as an encyclopedia or a dictionary. This is a more specific variant of the generic [`@collection`][Self::Collection] entry type. The standard styles will treat this entry type as an alias for [`@collection`][Self::Collection].
    Reference,
    /// BibLaTeX regular type: A multi-volume [`@reference`][Self::Reference] entry. The standard styles will treat this entry type as an alias for [`@mvcollection`][Self::MvCollection]. For backwards compatibility, multi-volume references are also supported by the entry type [`@reference`][Self::Reference]. However, it is advisable to make use of the dedicated entry type `@mvreference`.
    MvReference,
    /// BibLaTeX regular type: An article in a work of reference. This is a more specific variant of the generic [`@incollection`][Self::InCollection] entry type. The standard styles will treat this entry type as an alias for [`@incollection`][Self::InCollection].
    InReference,
    /// BibLaTeX regular type: A multi-volume [`@proceedings`][Self::Proceedings] entry. For backwards compatibility, multi-volume proceedings are also supported by the entry type [`@proceedings`][Self::Proceedings]. However, it is advisable to make use of the dedicated entry type `@mvproceedings`.
    MvProceedings,
    /// BibLaTeX regular type: A technical report, research report, or white paper published by a university or some other institution.
    Report,
    /// BibLaTeX regular type: A patent or patent request.
    Patent,
    /// BibLaTeX regular type: A thesis written for an educational institution to satisfy the requirements for a degree.
    Thesis,
    /// BibLaTeX regular type: An online resource. This entry type is intended for sources such as web sites which are intrinsically online resources. Note that all entry types support the `url` field. For example, when adding an article from an online journal, it may be preferable to use the [`@article`][Self::Article] type and its `url` field. `@electronic` is an alias for this type; `@www` is also an alias for this type, provided for `jurabib` compatibility.
    Online,
    /// BibLaTeX regular type: Computer software. The standard styles will treat this entry type as an alias for [`@misc`][Self::Misc].
    Software,
    /// BibLaTeX regular type: A data set or a similar collection of (mostly) raw data.
    Dataset,
    /// BibLaTeX regular type: An entry set. This entry type is special, see [§3.14.5 of `biblatex.pdf`][biblatex-3.14.5] for details.
    ///
    /// [biblatex-3.14.5]: https://mirrors.ctan.org/macros/latex/contrib/biblatex/doc/biblatex.pdf#subsubsection.3.14.5
    Set,
    /// BibLaTeX regular type: This entry type is special. `@xdata` entries hold data which may be inherited by other entries using the `xdata` field. Entries of this type only serve as data containers; they may not be cited or added to the bibliography. See [§3.14.6 of `biblatex.pdf`][biblatex-3.14.6] for details.
    ///
    /// [biblatex-3.14.6]: https://mirrors.ctan.org/macros/latex/contrib/biblatex/doc/biblatex.pdf#subsubsection.3.14.6
    XData,

    /// Unrecognized types.
    ///
    /// Examples:
    ///
    /// - [BibLaTeX non-standard types](https://mirrors.ctan.org/macros/latex/contrib/biblatex/doc/biblatex.pdf#subsubsection.2.1.3): `@artwork`, `@audio`, `@bibnote`, `@commentary`, `@image`, `@jurisdiction`, `@legislation`, `@legal`, `@letter`, `@movie`, `@music`, `@performance`, `@review`, `@standard`, `@video`.
    /// - Other custom types added by well-known implementations:
    ///   - [biblatex-apa](https://github.com/plk/biblatex-apa/blob/efb4437b2a58e47f3eb0729699e94b2b983a2291/tex/latex/biblatex-apa/dbx/apa.dbx#L18-L23): `@constitution`, `@legadminmaterial`, `@legmaterial`, `@nameonly`, `@presentation`
    ///   - [gbt7714-bibtex-style](https://mirrors.ctan.org/biblio/bibtex/contrib/gbt7714/gbt7714-doc.pdf#section.0.6): `@archive`, `@map`, `@preprint`
    ///   - [biblatex-gb7714-2025](https://mirrors.ctan.org/macros/latex/contrib/biblatex-contrib/biblatex-gb7714-2015/biblatex-gb7714-2015.pdf#subsubsection.4.3.6): `@newspaper`
    ///   - [Better BibTeX for Zotero](https://github.com/retorquere/zotero-better-bibtex/blob/7b7237e60aad44c47656484cd5eaa40201882449/translators/bibtex/bibtex.ts#L632-L683): `@book_section`, `@film`, `@generic`, `@magazine_article`, `@newspaper_article`, `@web_page` from Mendeley; `@webpage` from papers3; `@codefragment`, `@hardware`, `@softwaremodule`, `@softwareversion`, `@talk` from unknown sources
    ///
    /// This type should not be confused with [`@misc`][Self::Misc].
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
            // These aliases are documented on [`EntryType`].
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
///
/// Reference: Verbatim fields and URI fields, [2.2.1 Data Types — The `biblatex` Package (`biblatex.pdf`, v3.21, 2025-07-10) | CTAN](https://mirrors.ctan.org/macros/latex/contrib/biblatex/doc/biblatex.pdf#subsubsection.2.2.1)
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
