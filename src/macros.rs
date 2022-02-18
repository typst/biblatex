macro_rules! fields {
    ($($name:ident: $field:expr $(=> $ret:ty)?),* $(,)*) => {
        $(paste! {
            #[doc = "Get the `" $field "` field."]
            pub fn $name(&self) -> Option<fields!(@ret $($ret)?)> {
                self.get($field)$(?.parse::<$ret>())?
            }

            fields!(@set $name => $field, $($ret)?);
        })*
    };

    (@ret) => {&[Chunk]};
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
            pub fn $name(&self) -> Option<fields!(@ret $($ret)?)> {
                self.get($field)
                    .or_else(|| self.get($alias))
                    $(?.parse::<$ret>())?
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
            pub fn $name(&self) -> Option<Date> {
                if let Some(chunks) = self.get(concat!($prefix, "date")) {
                    chunks.parse::<Date>()
                } else {
                    Date::parse_three_fields(
                        self.get(concat!($prefix, "year"))?,
                        self.get(concat!($prefix, "month")),
                        self.get(concat!($prefix, "day")),
                    )
                }
            }

            #[doc = "Set the value of the `" $prefix "date` field, removing the
                     `" $prefix "year`, `" $prefix "month`, and
                     `" $prefix "day` fields if present."]
            pub fn [<set_ $name>](&mut self, item: Date) {
                self.set(concat!($prefix, "date"), item.to_chunks());
                self.remove(concat!($prefix, "year"));
                self.remove(concat!($prefix, "month"));
                self.remove(concat!($prefix, "day"));
            }
        })*
    };
}

pub(crate) use date_fields;
