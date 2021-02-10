use serde::{de, ser};
use std::fmt;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum NotYetImplemented {
    String(String),
    Array(Vec<NotYetImplemented>),
}

impl fmt::Debug for NotYetImplemented {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NotYetImplemented::String(string) => fmt::Debug::fmt(string, f),
            NotYetImplemented::Array(array) => fmt::Debug::fmt(array, f),
        }
    }
}

impl ser::Serialize for NotYetImplemented {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        match self {
            NotYetImplemented::String(string) => string.serialize(serializer),
            NotYetImplemented::Array(array) => array.serialize(serializer),
        }
    }
}

struct Visitor;
#[allow(unused)]
impl<'de> de::Visitor<'de> for Visitor {
    type Value = NotYetImplemented;
    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "anything")
    }

    fn visit_bool<E>(self, v: bool) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(NotYetImplemented::String(v.to_string()))
    }

    fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(NotYetImplemented::String(v.to_string()))
    }

    fn visit_u64<E>(self, v: u64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(NotYetImplemented::String(v.to_string()))
    }

    fn visit_f64<E>(self, v: f64) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(NotYetImplemented::String(v.to_string()))
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(NotYetImplemented::String(v.to_owned()))
    }

    // fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
    // where
    //     E: de::Error,
    // {
    //     let _ = v;
    //     Ok(NotYetImplemented::String(v.to_string()))
    // }

    fn visit_none<E>(self) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(NotYetImplemented::Array(Vec::new()))
    }

    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        Ok(NotYetImplemented::Array(vec![
            de::Deserialize::deserialize(deserializer)?,
        ]))
    }

    fn visit_unit<E>(self) -> Result<Self::Value, E>
    where
        E: de::Error,
    {
        Ok(NotYetImplemented::Array(Vec::new()))
    }

    fn visit_newtype_struct<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        Ok(NotYetImplemented::Array(vec![
            de::Deserialize::deserialize(deserializer)?,
        ]))
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: de::SeqAccess<'de>,
    {
        let mut result = Vec::new();
        while let Some(element) = seq.next_element()? {
            result.push(element);
        }
        Ok(NotYetImplemented::Array(result))
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: de::MapAccess<'de>,
    {
        let mut result = Vec::new();
        while let Some((key, value)) = map.next_entry()? {
            result.push(NotYetImplemented::Array(vec![key, value]));
        }
        Ok(NotYetImplemented::Array(result))
    }

    // fn visit_enum<A>(self, data: A) -> Result<Self::Value, A::Error>
    // where
    //     A: de::EnumAccess<'de>,
    // {
    //     let _ = data;
    //     Ok(NotYetImplemented::String(v.to_string()))
    // }
}
impl<'de> de::Deserialize<'de> for NotYetImplemented {
    fn deserialize<D: de::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_any(Visitor)
    }
}
