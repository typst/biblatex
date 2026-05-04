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
