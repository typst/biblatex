use std::str::FromStr;

use strum::{Display, EnumString};

use super::{Type, TypeError, TypeErrorKind};
use crate::{Chunk, Chunks, ChunksExt, ChunksRef, Spanned};

macro_rules! languages {
    ($($id:ident ($doc:literal) => $val:literal $(| $alias:literal)*),*) => {
        /// The languages supported by biblatex
        #[derive(Debug, Copy, Clone, Eq, PartialEq, Display, EnumString)]
        pub enum Language {
          $(
            #[doc = $doc]
            #[strum(to_string = $doc, serialize = $val, $(serialize = $alias),*)]
            $id
          ),*
        }

        impl Type for Language {
          fn from_chunks(chunks: ChunksRef) -> Result<Self, TypeError> {
            let span = chunks.span();
            Self::from_str(&chunks.format_verbatim())
              .map_err(|_| TypeError::new(span, TypeErrorKind::UnknownLangId))
          }

          fn to_chunks(&self) -> Chunks {
            vec![Spanned::detached(Chunk::Verbatim(self.to_string()))]
          }
        }
    };
}

languages! {
  Basque ("Basque") => "basque",
  Bulgarian ("Bulgarian") => "bulgarian",
  Catalan ("Catalan") => "catalan",
  Croatian ("Croatian") => "croation",
  Czech ("Czech") => "czech",
  Danish ("Danish") => "danish",
  Dutch ("Dutch") => "dutch",
  EnglishUS ("American English") => "american" | "USenglish" | "english",
  EnglishUK ("British English") => "british" | "UKenglish",
  EnglishAUS ("Australian English") => "australian",
  EnglishNZ ("New Zealand English") => "newzealand",
  Estonian ("Estonian") => "estonian",
  Finnish ("Finnish") => "finnish",
  French ("French") => "french",
  German ("German") => "german",
  GermanAT ("Austrian") => "austrian",
  GermanCH ("Swiss German") => "swissgerman",
  GermanNew ("New German") => "ngerman",
  GermanATNew ("New Austrian") => "naustrian",
  GermanCHNew ("New Swiss German") => "nswissgerman",
  Greek ("Greek") => "greek",
  Hungarian ("Hungarian") => "magyar" | "hungarian",
  Icelandic ("Icelandic") => "icelandic",
  Italian ("Italian") => "italian",
  Latvian ("Latvian") => "latvian",
  Lithuanian ("Lithuanian") => "lithuanian",
  Marathi ("Marathi") => "marathi",
  NorwegianBokmal ("Norwegian (Bokmål)") => "norsk",
  NorwegainNynorsk ("Norwegian (Nynorsk)") => "nynorsk",
  Polish ("Polish") => "polish",
  PortugueseBR ("Brazilian Portuguese") => "brazil",
  Portuguese ("Portuguese") => "portuguese" | "portuges",
  Romanian ("Romanian") => "romanian",
  Russian ("Russian") => "russian",
  SerbianLatin ("Serbian (Latin)") => "serbian",
  SerbianCyrillic ("Serbian (Cyrillic)") => "serbianc",
  Slovak ("Slovak") => "slovak",
  Slovene ("Slovene") => "slovene" | "slovanian",
  Spanish ("Spanish") => "spanish",
  Swedish ("Swedish") => "swedish",
  Turkish ("Turkish") => "turkish",
  Ukranian ("Ukranian") => "ukranian"
}

#[cfg(test)]
mod tests {
    use crate::Language;

    #[test]
    fn aliases() {
        assert_eq!(Language::EnglishUS, "english".parse().unwrap());
        assert_eq!(Language::Portuguese, "portuges".parse().unwrap())
    }
}
