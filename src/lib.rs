pub mod dtypes;
pub mod parse;
pub mod syntax;

#[cfg(test)]
mod tests {
    use std::fs;

    use crate::dtypes::format_sentence;
    use crate::parse::parse_collection;

    #[test]
    fn test_gral_paper() {
        dump_debug("test/gral.bib");
    }

    #[test]
    fn test_ds_report() {
        dump_debug("test/ds.bib");
    }

    #[test]
    fn test_libra_paper() {
        dump_author_title("test/libra.bib");
    }

    #[test]
    fn test_rass_report() {
        dump_author_title("test/rass.bib");
    }

    fn dump_debug(file: &str) {
        let contents = fs::read_to_string(file).unwrap();
        let collection = parse_collection(&contents, true);
        println!("{:#?}", collection);
    }

    fn dump_author_title(file: &str) {
        let contents = fs::read_to_string(file).unwrap();
        let collection = parse_collection(&contents, true);

        for x in collection {
            let authors = x.get_author().unwrap_or_default();
            for a in authors {
                print!("{}, ", a);
            }
            println!("\"{}\".", format_sentence(&x.get_title().unwrap()));
        }
    }
}
