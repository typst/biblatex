pub mod fields;
pub mod parse;
pub mod syntax;

use crate::syntax::BiblatexParser;

#[cfg(test)]
mod tests {
    use crate::fields;
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

        println!("{:#?}", bt);
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

        println!("{:#?}", bt);

        for x in bt {
            for y in x.1.props {
                if y.0.to_lowercase() == "author" {
                    println!(
                        "{:?}",
                        fields::split_token_lists(y.1)
                            .iter()
                            .map(|x| fields::format_verbatim(x))
                            .collect::<Vec<String>>()
                    );
                }
            }
        }
    }
}
