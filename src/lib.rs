#[macro_use]
extern crate lazy_static;
extern crate strum;
#[macro_use]
extern crate anyhow;

pub mod dtypes;
pub mod fields;
pub mod parse;
pub mod syntax;

use crate::syntax::BiblatexParser;

#[cfg(test)]
mod tests {
    use crate::dtypes::format_sentence;
    use crate::parse::new_collection;
    use std::fs;

    #[test]
    fn ds_report() {
        let contents = fs::read_to_string("test/ds.bib").expect("File not found");
        let bt = new_collection(&contents, true);

        println!("{:#?}", bt);
    }

    #[test]
    fn rass_report() {
        let contents = fs::read_to_string("test/rass.bib").expect("File not found");
        let bt = new_collection(&contents, true);

        for x in bt {
            let authors = x.1.get_author().unwrap_or(vec![]);

            for a in authors {
                print!("{}, ", a)
            }
            println!("\"{}\".", format_sentence(&x.1.get_title().unwrap()));
        }
    }

    #[test]
    fn gral_paper() {
        let contents = fs::read_to_string("test/gral.bib").expect("File not found");
        let bt = new_collection(&contents, true);

        println!("{:#?}", bt);
    }

    #[test]
    fn libra_paper() {
        let contents = fs::read_to_string("test/libra.bib").expect("File not found");
        let bt = new_collection(&contents, true);

        // println!("{:#?}", bt);

        for x in bt {
            let authors = x.1.get_author().unwrap_or(vec![]);

            for a in authors {
                print!("{}, ", a)
            }
            println!("\"{}\".", format_sentence(&x.1.get_title().unwrap()));
        }
    }
}
