use std::fs;

use biblatex::{Bibliography, ChunksExt};

#[test]
fn test_gral_paper() {
    dump_debug("tests/fixtures/valid/gral.bib");
}

#[test]
fn test_ds_report() {
    dump_debug("tests/fixtures/valid/ds.bib");
}

#[test]
fn test_libra_paper() {
    dump_author_title("tests/fixtures/valid/libra.bib");
}

#[test]
fn test_rass_report() {
    dump_author_title("tests/fixtures/valid/rass.bib");
}

#[test]
fn test_polar_report() {
    dump_author_title("tests/fixtures/valid/polaritons.bib");
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
fn test_extended_name_format() {
    dump_author_title("tests/fixtures/valid/extended_name_format.bib");
}
