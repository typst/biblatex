# BibLaTeX

[![Build status](https://github.com/typst/biblatex/workflows/Continuous%20integration/badge.svg)](https://github.com/typst/biblatex/actions)
[![Current crates.io release](https://img.shields.io/crates/v/biblatex)](https://crates.io/crates/biblatex)
[![Documentation](https://img.shields.io/badge/docs.rs-biblatex-66c2a5?labelColor=555555&logoColor=white&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K)](https://docs.rs/biblatex/)

A Rust crate for parsing and writing BibTeX and BibLaTeX files.

BibLaTeX can help you to parse `.bib` bibliography files.
As opposed to other available crates, this crate attempts to parse the data
within the fields into easily usable structs and enums like `Person` and `Date`
for downstream consumption.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
biblatex = "0.9"
```

Parsing a bibliography and getting the author of an item is as simple as:

```rust
let src = "@book{tolkien1937, author = {J. R. R. Tolkien}}";
let bibliography = Bibliography::parse(src).unwrap();
let entry = bibliography.get("tolkien1937").unwrap();
let author = entry.author().unwrap();
assert_eq!(author[0].name, "Tolkien");
```

This library operates on a `Bibliography` struct, which is a collection of
_entries_ (the items in your `.bib` file that start with an `@` and are wrapped
in curly braces). The entries may hold multiple fields. Entries have getter
methods for each of the possible fields in a Bib(La)TeX file which handle
possible field aliases, composition and type conversion automatically.

Refer to the [WikiBook section on LaTeX bibliography management](https://en.wikibooks.org/wiki/LaTeX/Bibliography_Management)
and the [BibLaTeX package manual](http://ctan.ebinger.cc/tex-archive/macros/latex/contrib/biblatex/doc/biblatex.pdf)
to learn more about the intended meaning of each of the fields.

The generated documentation more specifically describes the selection and
behavior of the getters but generally, they follow the convention of being the
snake-case name of the corresponding field
(such that the getter for `booktitleaddon` is named `book_title_addon`).

## Limitations

This library attempts to provide fairly comprehensive coverage of the BibLaTeX
spec with which most of the `.bib` files in circulation can be processed.

However, the crate currently has some limitations:

- There is no explicit support for entry sets, although it is easy to account
  for them by manually getting the `entryset` field and calling
  `parse::<Vec<String>>()` on it
