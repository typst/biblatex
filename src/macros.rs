macro_rules! fields {
    ($($name:ident: $field:expr $(=> $ret:ty)?),* $(,)*) => {
        $(paste! {
            #[doc = "Get the `" $field "` field."]
            pub fn $name(&self) -> Result<fields!(@ret $($ret)?), RetrievalError> {
                self
                    .get($field)
                    .ok_or_else(|| RetrievalError::Missing($field.to_string()))
                    $(?.parse::<$ret>().map_err(Into::into))?
            }

            fields!(@set $name => $field, $($ret)?);
        })*
    };

    (@ret) => {ChunksRef<'_>};
    (@ret $ret:ty) => {$ret};

    (@set $name:ident => $field:literal, ) => {
        paste! {
            #[doc = "Set the value of the `" $field "` field."]
            pub fn [<set_ $name>](&mut self, item: Chunks) {
                self.set($field, item);
            }
        }
    };
    (@set $name:ident => $field:literal, $ty:ty) => {
        paste! {
            #[doc = "Set the value of the `" $field "` field."]
            pub fn [<set_ $name>](&mut self, item: $ty) {
                self.set($field, item.to_chunks());
            }
        }
    };
}

pub(crate) use fields;

macro_rules! alias_fields {
    ($($name:ident: $field:literal | $alias:literal $(=> $ret:ty)?),* $(,)*) => {
        $(paste! {
            #[doc = "Get the `" $field "` field, falling back on `" $alias "`
                     if `" $field "` is empty."]
            pub fn $name(&self) -> Result<fields!(@ret $($ret)?), RetrievalError> {
                self.get($field)
                    .or_else(|| self.get($alias))
                    .ok_or_else(|| RetrievalError::Missing($field.to_string()))
                    $(?.parse::<$ret>().map_err(Into::into))?
            }

            fields!(@set $name => $field, $($ret)?);
        })*
    };
}

pub(crate) use alias_fields;

macro_rules! date_fields {
    ($($name:ident: $prefix:literal),* $(,)*) => {
        $(paste! {
            #[doc = "Get the `" $prefix "date` field, falling back on the
                     `" $prefix "year`, `" $prefix "month`, and
                     `" $prefix "day` fields if it is not present."]
            pub fn $name(&self) -> Result<PermissiveType<Date>, RetrievalError> {
                if let Some(chunks) = self.get(concat!($prefix, "date")) {
                    chunks.parse::<Date>()
                        .map(|d| PermissiveType::Typed(d))
                        .or_else(|_| Ok::<_, RetrievalError>(PermissiveType::Chunks(chunks.to_vec())))
                } else {
                    let year = self.get(concat!($prefix, "year")).ok_or_else(|| RetrievalError::Missing("year".to_string()))?;
                    let month = self.get(concat!($prefix, "month"));
                    let day = self.get(concat!($prefix, "day"));

                    let parsed = Date::parse_three_fields(year, month, day);
                    match (parsed, year, month, day) {
                        (Ok(date), ..) => Ok(PermissiveType::Typed(date)),
                        // Some conventions put literal dates in the `year` field
                        // due to biblatex intricacies. See https://github.com/typst/biblatex/issues/105
                        // for the detail.
                        // Therefore, if the format is invalid and only `year`
                        // is provided, then it should be treated as literal.
                        (
                            Err(TypeError { kind: TypeErrorKind::InvalidFormat, .. }),
                            year,
                            None,
                            None,
                        ) => Ok(PermissiveType::Chunks(year.to_vec())),
                        // Dates in regular formats should still be rejected if
                        // they have errors like `MonthOutOfRange`.
                        (Err(err), ..) => Err(err.into()),
                    }
                }.map_err(Into::into)
            }

            #[doc = "Set the value of the `" $prefix "date` field, removing the
                     `" $prefix "year`, `" $prefix "month`, and
                     `" $prefix "day` fields if present."]
            pub fn [<set_ $name>](&mut self, item: PermissiveType<Date>) {
                self.set(concat!($prefix, "date"), item.to_chunks());
                self.remove(concat!($prefix, "year"));
                self.remove(concat!($prefix, "month"));
                self.remove(concat!($prefix, "day"));
            }
        })*
    };
}

pub(crate) use date_fields;
