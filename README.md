# BibLaTeX

[![Build status](https://github.com/typst/biblatex/workflows/Continuous%20integration/badge.svg)](https://github.com/typst/biblatex/actions)

A Rust crate for parsing and writing BibTeX and BibLaTeX files.

BibLaTeX can help you to parse `.bib` bibliography files.
As opposed to other available crates, this crate attempts to parse the data
within the fields into easily usable structs and enums like `Person` and `Date`
for downstream consumption.

## Install

This crate is to be published on Crates.io.
In the meantime, the user may clone this repository and use it as a dependency locally.

## Usage

Parsing a bibliography and getting the author of an item is as simple as:

```rust
let bibliography = Bibliography::from_str(bib_file_str, true);
let author = bibliography.get("some_cite_key").unwrap().get_author(); // Returns an Result<Person, anyhow::Error>
```

This library operates on the Bibliography struct, which is a vector of entries
(the items in your `.bib` file that start with an `@` and are wrapped in curly
braces).
The entries may hold multiple fields.
Each entry has getter methods corresponding to each of the possible fields in
a Bib(La)TeX file which handle possible field aliases, composition and type
conversion automatically.

Refer to the [WikiBook section on LaTeX bibliography management](https://en.wikibooks.org/wiki/LaTeX/Bibliography_Management)
and the [BibLaTeX package manual](http://ctan.ebinger.cc/tex-archive/macros/latex/contrib/biblatex/doc/biblatex.pdf)
to learn more about the intended meaning of each of the fields.

The generated documentation more specifically describes the selection and
behavior of the getters but generally, they follow the convention of being the
snake-case name of the corresponding field with 'get' prepended
(such that the getter for `booktitleaddon` is named `get_book_title_addon`).

## Limitations

This library attempts to provide fairly comprehensive coverage of the BibLaTeX
spec with which most of the `.bib` files in circulation can be processed.

However, the crate currently has some limitations:

- Nested TeX commands are not supported
- Math mode formatting is not being processed, instead, the output strings will
  contain the dollar-delimited math syntax as it is found in the input string.
- Secondary cite keys (`ids` field) are not yet supported
- `Crossref` (as well as `xref` and `xdata`) citing is not yet supported (i.e.
  inheriting an items properties to a child)
- There is no explicit support for entry sets, although it is easy to account
  for them by manually getting the `entryset` field and calling
  `parse::<Vec<String>>()` on it