use std::fs;

use biblatex::{
    Bibliography, ParseError, ParseErrorKind, RetrievalError, Token, TypeError,
    TypeErrorKind,
};

#[test]
fn test_repeated_key() {
    let contents = fs::read_to_string("tests/fixtures/invalid/gral_rep_key.bib").unwrap();
    let bibliography = Bibliography::parse(&contents);
    match bibliography {
        Ok(_) => panic!("Should return Err"),
        Err(s) => {
            assert_eq!(s.kind, ParseErrorKind::DuplicateKey("ishihara2012".into()));
        }
    };
}

#[test]
fn test_self_referential_crossref() {
    let contents = "@incollection{Hartman2022, crossref = {Hartman2022}}";

    assert_eq!(
        Bibliography::parse(contents).unwrap_err().kind,
        ParseErrorKind::CircularReference("Hartman2022".into()),
    );
}

#[test]
fn test_indirect_crossref_cycle() {
    let contents = r#"
        @incollection{a, crossref = {b}}
        @collection{b, crossref = {a}}
    "#;

    assert_eq!(
        Bibliography::parse(contents).unwrap_err().kind,
        ParseErrorKind::CircularReference("a".into()),
    );
}

#[test]
fn test_parse_incorrect_result() {
    let contents = fs::read_to_string("tests/fixtures/invalid/incorrect_syntax.bib")
        .unwrap()
        .replace("\r\n", "\n");

    let bibliography = Bibliography::parse(&contents);
    match bibliography {
        Ok(_) => {
            panic!("Should return Err")
        }
        Err(s) => {
            assert_eq!(
                s,
                ParseError {
                    span: 369..369,
                    kind: ParseErrorKind::Expected(Token::Equals)
                }
            );
        }
    };
}

#[test]
fn test_parse_incorrect_types() {
    let contents = fs::read_to_string("tests/fixtures/invalid/incorrect_data.bib")
        .unwrap()
        .replace("\r\n", "\n");

    let bibliography = Bibliography::parse(&contents).unwrap();
    let rashid = bibliography.get("rashid2016").unwrap();
    match rashid.pagination() {
        Err(RetrievalError::TypeError(s)) => {
            assert_eq!(
                s,
                TypeError {
                    span: 352..359,
                    kind: TypeErrorKind::UnknownPagination
                }
            )
        }
        _ => {
            panic!()
        }
    };
}
