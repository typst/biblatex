use std::fs;

use biblatex::{
    Bibliography, Chunk, ChunksExt, EditorType, Entry, EntryType, PermissiveType, Person,
    RetrievalError, TypeError, TypeErrorKind,
};

#[test]
fn test_correct_bib() {
    let contents = fs::read_to_string("tests/gral.bib").unwrap();
    let bibliography = Bibliography::parse(&contents).unwrap();
    assert_eq!(bibliography.len(), 83)
}

#[test]
fn test_keys() {
    let contents = fs::read_to_string("tests/editortypes.bib").unwrap();

    let bibliography = Bibliography::parse(&contents).unwrap();

    assert_eq!(
        bibliography.keys().collect::<Vec<_>>(),
        &["acerolaThisDifferenceGaussians2022", "mozart_KV183_1773", "Smith2018"]
    );
}

#[test]
fn test_comments() {
    let contents = fs::read_to_string("tests/comments.bib").unwrap();

    let bibliography = Bibliography::parse(&contents).unwrap();

    assert_eq!(
        bibliography.keys().collect::<Vec<_>>(),
        &[
            "mcelreath2007mathematical",
            "fischer2022equivalence",
            "roes2003belief",
            "wong2016null",
        ]
    );

    assert_eq!(
        bibliography
            .get("wong2016null")
            .unwrap()
            .title()
            .unwrap()
            .format_verbatim(),
        "Null hypothesis testing (I)-5% significance level"
    );
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

    let bibtex = bibliography.get_mut("haug2019").unwrap().to_bibtex_string().unwrap();
    assert!(bibtex.contains("school = {Technische Universität Berlin},"));
    assert!(bibtex.contains("year = {2019},"));
    assert!(bibtex.contains("month = {10},"));
    assert!(!bibtex.contains("institution"));
    assert!(!bibtex.contains("date"));
}

#[test]
fn test_verify() {
    let mut contents = fs::read_to_string("tests/gral.bib").unwrap();
    let mut bibliography = Bibliography::parse(&contents).unwrap();
    assert!(bibliography.get_mut("lin_sida:_2007").unwrap().verify().is_ok());

    contents = fs::read_to_string("tests/cross.bib").unwrap();
    bibliography = Bibliography::parse(&contents).unwrap();

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
        );

    // Test URLs with math and backslashes
    let e = bibliography.get("weirdUrl2023").unwrap();
    assert_eq!(e.url().unwrap(), r#"example.com?A=$B\%\{}"#);
    assert_eq!(e.doi().unwrap(), r#"example.com?A=$B\%\{}"#);
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
        Err(TypeError { span: 74..74, kind: TypeErrorKind::MissingNumber }.into())
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

#[test]
fn test_editor_types() {
    let contents = fs::read_to_string("tests/editortypes.bib").unwrap();
    let bibliography = Bibliography::parse(&contents).unwrap();
    let video = bibliography.get("acerolaThisDifferenceGaussians2022").unwrap();
    assert_eq!(
        video.editors(),
        Ok(vec![(
            vec![Person {
                name: "Acerola".into(),
                given_name: "".into(),
                prefix: "".into(),
                suffix: "".into()
            }],
            EditorType::Director
        )])
    );

    let music = bibliography.get("mozart_KV183_1773").unwrap();
    assert_eq!(
        music.editors(),
        Ok(vec![(
            vec![Person {
                name: "Mozart".into(),
                given_name: "Wolfgang Amadeus".into(),
                prefix: "".into(),
                suffix: "".into()
            }],
            EditorType::Unknown("pianist".into()),
        )])
    );

    let audio = bibliography.get("Smith2018").unwrap();
    assert_eq!(
        audio.editors(),
        Ok(vec![
            (
                vec![Person {
                    name: "Smith".into(),
                    given_name: "Stacey Vanek".into(),
                    prefix: "".into(),
                    suffix: "".into()
                }],
                EditorType::Unknown("host".into()),
            ),
            (
                vec![Person {
                    name: "Plotkin".into(),
                    given_name: "Stanley".into(),
                    prefix: "".into(),
                    suffix: "".into()
                }],
                EditorType::Unknown("participant".into()),
            )
        ])
    );
}
