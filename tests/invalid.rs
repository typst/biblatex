use std::fs;

use biblatex::{
    Bibliography, ParseError, ParseErrorKind, RetrievalError, Token, TypeError,
    TypeErrorKind,
};

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
// FIXME: new is private is parse error
// #[test]
// fn test_parse_incorrect_result() {
//     let contents = fs::read_to_string("tests/incorrect_syntax.bib").unwrap();

//     let bibliography = Bibliography::parse(&contents);
//     match bibliography {
//         Ok(_) => {
//             panic!("Should return Err")
//         }
//         Err(s) => {
//             assert_eq!(
//                 s,
//
//                 ParseError::new(369..369, ParseErrorKind::Expected(Token::Equals))
//             );
//         }
//     };
// }

// FIXME: new is private in type error
// #[test]
// fn test_parse_incorrect_types() {
//     let contents = fs::read_to_string("tests/incorrect_data.bib").unwrap();

//     let bibliography = Bibliography::parse(&contents).unwrap();
//     let rashid = bibliography.get("rashid2016").unwrap();
//     match rashid.pagination() {
//         Err(RetrievalError::TypeError(s)) => {
//
//             assert_eq!(s, TypeError::new(352..359, TypeErrorKind::UnknownPagination));
//         }
//         _ => {
//             panic!()
//         }
//     };
// }
