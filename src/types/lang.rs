use std::str::FromStr;

use strum::{Display, EnumString};

#[cfg(feature = "unic-langid")]
use unic_langid::{langid, LanguageIdentifier};

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
  Croatian ("Croatian") => "croatian",
  Czech ("Czech") => "czech",
  Danish ("Danish") => "danish",
  Dutch ("Dutch") => "dutch",
  EnglishUS ("American English") => "american" | "USenglish" | "english",
  EnglishUK ("British English") => "british" | "UKenglish",
  EnglishCA ("Canadian English") => "canadian",
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

#[cfg(feature = "unic-langid")]
impl From<Language> for LanguageIdentifier {
    fn from(value: Language) -> Self {
        match value {
            Language::Basque => langid!("eu"),
            Language::Bulgarian => langid!("bg"),
            Language::Catalan => langid!("ca"),
            Language::Croatian => langid!("hr"),
            Language::Czech => langid!("cs"),
            Language::Danish => langid!("da"),
            Language::Dutch => langid!("nl"),
            Language::EnglishUS => langid!("en-US"),
            Language::EnglishUK => langid!("en-UK"),
            Language::EnglishCA => langid!("en-CA"),
            Language::EnglishAUS => langid!("en-AU"),
            Language::EnglishNZ => langid!("en-NZ"),
            Language::Estonian => langid!("et"),
            Language::Finnish => langid!("fi"),
            Language::French => langid!("fr"),
            Language::German | Language::GermanNew => langid!("de"),
            Language::GermanAT | Language::GermanATNew => langid!("de-AT"),
            Language::GermanCH | Language::GermanCHNew => langid!("de-CH"),
            Language::Greek => langid!("el"),
            Language::Hungarian => langid!("hu"),
            Language::Icelandic => langid!("is"),
            Language::Italian => langid!("it"),
            Language::Latvian => langid!("lv"),
            Language::Lithuanian => langid!("lt"),
            Language::Marathi => langid!("mr"),
            Language::NorwegianBokmal => langid!("nb"),
            Language::NorwegainNynorsk => langid!("nn"),
            Language::Polish => langid!("pl"),
            Language::PortugueseBR => langid!("pt-BR"),
            Language::Portuguese => langid!("pt-PT"),
            Language::Romanian => langid!("ro"),
            Language::Russian => langid!("ru"),
            Language::SerbianLatin => langid!("sr-LATIN"),
            Language::SerbianCyrillic => langid!("sr-CYRILLIC"),
            Language::Slovak => langid!("sk"),
            Language::Slovene => langid!("sl"),
            Language::Spanish => langid!("es"),
            Language::Swedish => langid!("sv"),
            Language::Turkish => langid!("tr"),
            Language::Ukranian => langid!("uk"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Language;

    #[test]
    fn aliases() {
        assert_eq!(Language::EnglishUS, "english".parse().unwrap());
        assert_eq!(Language::Portuguese, "portuges".parse().unwrap())
    }

    #[cfg(feature = "unic-langid")]
    #[test]
    fn langid() {
        use unic_langid::LanguageIdentifier;

        let lang: Language = "ngerman".parse().unwrap();
        let id: LanguageIdentifier = lang.into();
        assert_eq!("de", id.to_string());
    }
}
