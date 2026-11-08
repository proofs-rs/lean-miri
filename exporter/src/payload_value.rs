//! Persistent semantic JSON values used while collecting exporter evidence.
//!
//! Cloning a container copies one Arc. Mutating one occurrence uses copy on
//! write, leaving cached/compiler evidence and other occurrences unchanged.
//! The sharing registry owns canonicalization and wire references; `Plain`
//! deliberately bypasses that registry for semantic diagnostics and keys.

use serde::ser::{SerializeMap, SerializeSeq};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde_json::{Number, Value as RawValue};
use std::collections::BTreeMap;
use std::fmt;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::sync::Arc;

pub type Map<K = String, V = Value> = BTreeMap<K, V>;

#[derive(Debug)]
pub struct Shared<T>(Arc<T>);

impl<T> Clone for Shared<T> {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}
impl<T> From<T> for Shared<T> {
    fn from(value: T) -> Self {
        Self(Arc::new(value))
    }
}
impl<T: Default> Default for Shared<T> {
    fn default() -> Self {
        Self::from(T::default())
    }
}
impl<T> AsRef<T> for Shared<T> {
    fn as_ref(&self) -> &T {
        self.0.as_ref()
    }
}
impl<T: Clone> AsMut<T> for Shared<T> {
    fn as_mut(&mut self) -> &mut T {
        Arc::make_mut(&mut self.0)
    }
}
impl<T: Serialize> Serialize for Shared<T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.as_ref().serialize(serializer)
    }
}
impl<T: fmt::Display> fmt::Display for Shared<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.as_ref().fmt(formatter)
    }
}
impl<T> Deref for Shared<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}
impl<T: Clone> DerefMut for Shared<T> {
    fn deref_mut(&mut self) -> &mut T {
        Arc::make_mut(&mut self.0)
    }
}
impl<T: PartialEq> PartialEq for Shared<T> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.0.as_ref() == other.0.as_ref()
    }
}
impl<T: Eq> Eq for Shared<T> {}
impl<'a, T> IntoIterator for &'a Shared<T>
where
    &'a T: IntoIterator,
{
    type Item = <&'a T as IntoIterator>::Item;
    type IntoIter = <&'a T as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.deref().into_iter()
    }
}
impl<'a, T: Clone> IntoIterator for &'a mut Shared<T>
where
    &'a mut T: IntoIterator,
{
    type Item = <&'a mut T as IntoIterator>::Item;
    type IntoIter = <&'a mut T as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.deref_mut().into_iter()
    }
}
impl<T: Clone> IntoIterator for Shared<Vec<T>> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        Arc::try_unwrap(self.0)
            .unwrap_or_else(|shared| shared.as_ref().clone())
            .into_iter()
    }
}
impl<K: Ord + Clone, V: Clone> IntoIterator for Shared<BTreeMap<K, V>> {
    type Item = (K, V);
    type IntoIter = std::collections::btree_map::IntoIter<K, V>;
    fn into_iter(self) -> Self::IntoIter {
        Arc::try_unwrap(self.0)
            .unwrap_or_else(|shared| shared.as_ref().clone())
            .into_iter()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub enum Value {
    #[default]
    Null,
    Bool(bool),
    Number(Number),
    String(Shared<String>),
    Array(Shared<Vec<Value>>),
    Object(Shared<Map>),
}

impl Value {
    pub fn array(values: Vec<Value>) -> Self {
        crate::payload_sharing::canonicalize(Self::Array(values.into()))
    }
    pub fn object(values: Map) -> Self {
        crate::payload_sharing::canonicalize(Self::Object(values.into()))
    }
    pub fn string(value: String) -> Self {
        crate::payload_sharing::canonicalize(Self::String(value.into()))
    }
    /// Identity is confined to this process. The registry retains canonical
    /// nodes while using their addresses, so it must not outlive that ownership.
    pub fn identity(&self) -> Option<(u8, usize)> {
        match self {
            Self::String(value) => Some((0, Arc::as_ptr(&value.0) as usize)),
            Self::Array(value) => Some((1, Arc::as_ptr(&value.0) as usize)),
            Self::Object(value) => Some((2, Arc::as_ptr(&value.0) as usize)),
            _ => None,
        }
    }
    /// Convert macro serialization back into semantic values. References here
    /// use the private collection handle, never the public wire-reference key.
    pub fn from_wire(value: RawValue) -> Self {
        if let RawValue::Object(object) = &value {
            if object.len() == 1 {
                if let Some(id) = object.get(crate::payload_sharing::HANDLE) {
                    if crate::payload_sharing::has_invalid() {
                        return Self::from_raw(value);
                    }
                    let id = id
                        .as_u64()
                        .and_then(|id| usize::try_from(id).ok())
                        .expect("internal shared reference must contain a valid node ID");
                    return crate::payload_sharing::lookup_node(id)
                        .expect("internal shared reference must belong to the active registry");
                }
            }
        }
        match value {
            RawValue::Null => Self::Null,
            RawValue::Bool(value) => Self::Bool(value),
            RawValue::Number(value) => Self::Number(value),
            RawValue::String(value) => Self::string(value),
            RawValue::Array(values) => {
                Self::array(values.into_iter().map(Self::from_wire).collect())
            }
            RawValue::Object(values) => Self::object(
                values
                    .into_iter()
                    .map(|(key, value)| (key, Self::from_wire(value)))
                    .collect(),
            ),
        }
    }
    /// Deserialize ordinary data without interpreting reserved reference keys.
    pub fn from_raw(value: RawValue) -> Self {
        match value {
            RawValue::Null => Self::Null,
            RawValue::Bool(value) => Self::Bool(value),
            RawValue::Number(value) => Self::Number(value),
            RawValue::String(value) => Self::string(value),
            RawValue::Array(values) => {
                Self::array(values.into_iter().map(Self::from_raw).collect())
            }
            RawValue::Object(values) => Self::object(
                values
                    .into_iter()
                    .map(|(key, value)| (key, Self::from_raw(value)))
                    .collect(),
            ),
        }
    }
    pub fn as_object(&self) -> Option<&Map> {
        match self {
            Self::Object(value) => Some(value),
            _ => None,
        }
    }
    pub fn as_object_mut(&mut self) -> Option<&mut Map> {
        match self {
            Self::Object(value) => Some(value),
            _ => None,
        }
    }
    pub fn as_array(&self) -> Option<&Vec<Value>> {
        match self {
            Self::Array(value) => Some(value),
            _ => None,
        }
    }
    pub fn as_array_mut(&mut self) -> Option<&mut Vec<Value>> {
        match self {
            Self::Array(value) => Some(value),
            _ => None,
        }
    }
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::String(value) => Some(value.as_str()),
            _ => None,
        }
    }
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(value) => Some(*value),
            _ => None,
        }
    }
    pub fn as_number(&self) -> Option<&Number> {
        match self {
            Self::Number(value) => Some(value),
            _ => None,
        }
    }
    pub fn as_u64(&self) -> Option<u64> {
        self.as_number().and_then(Number::as_u64)
    }
    pub fn as_i64(&self) -> Option<i64> {
        self.as_number().and_then(Number::as_i64)
    }
    pub fn as_f64(&self) -> Option<f64> {
        self.as_number().and_then(Number::as_f64)
    }
    pub fn as_null(&self) -> Option<()> {
        self.is_null().then_some(())
    }
    pub fn is_object(&self) -> bool {
        matches!(self, Self::Object(_))
    }
    pub fn is_array(&self) -> bool {
        matches!(self, Self::Array(_))
    }
    pub fn is_string(&self) -> bool {
        matches!(self, Self::String(_))
    }
    pub fn is_boolean(&self) -> bool {
        matches!(self, Self::Bool(_))
    }
    pub fn is_number(&self) -> bool {
        matches!(self, Self::Number(_))
    }
    pub fn is_null(&self) -> bool {
        matches!(self, Self::Null)
    }
    pub fn is_u64(&self) -> bool {
        self.as_number().is_some_and(Number::is_u64)
    }
    pub fn is_i64(&self) -> bool {
        self.as_number().is_some_and(Number::is_i64)
    }
    pub fn is_f64(&self) -> bool {
        self.as_number().is_some_and(Number::is_f64)
    }
    pub fn get<I: ValueIndex>(&self, index: I) -> Option<&Value> {
        index.get(self)
    }
    pub fn get_mut<I: ValueIndex>(&mut self, index: I) -> Option<&mut Value> {
        index.get_mut(self)
    }
    pub fn take(&mut self) -> Value {
        std::mem::take(self)
    }
    pub fn pointer(&self, pointer: &str) -> Option<&Value> {
        if pointer.is_empty() {
            return Some(self);
        }
        if !pointer.starts_with('/') {
            return None;
        }
        let mut current = self;
        for part in pointer[1..].split('/') {
            let key = part.replace("~1", "/").replace("~0", "~");
            current = match current {
                Self::Object(object) => object.get(&key)?,
                Self::Array(values) => values.get(array_index(&key)?)?,
                _ => return None,
            };
        }
        Some(current)
    }
    pub fn pointer_mut(&mut self, pointer: &str) -> Option<&mut Value> {
        if pointer.is_empty() {
            return Some(self);
        }
        if !pointer.starts_with('/') {
            return None;
        }
        let mut current = self;
        for part in pointer[1..].split('/') {
            let key = part.replace("~1", "/").replace("~0", "~");
            current = match current {
                Self::Object(object) => object.get_mut(&key)?,
                Self::Array(values) => values.get_mut(array_index(&key)?)?,
                _ => return None,
            };
        }
        Some(current)
    }
}

fn array_index(token: &str) -> Option<usize> {
    if token.is_empty() || token.starts_with('+') || (token.len() > 1 && token.starts_with('0')) {
        None
    } else {
        token.parse().ok()
    }
}

/// The same object/array indexing contract used by serde_json::Value.
pub trait ValueIndex {
    fn get<'v>(&self, value: &'v Value) -> Option<&'v Value>;
    fn get_mut<'v>(&self, value: &'v mut Value) -> Option<&'v mut Value>;
    fn get_or_insert<'v>(&self, value: &'v mut Value) -> &'v mut Value;
}
impl ValueIndex for usize {
    fn get<'v>(&self, value: &'v Value) -> Option<&'v Value> {
        value.as_array()?.get(*self)
    }
    fn get_mut<'v>(&self, value: &'v mut Value) -> Option<&'v mut Value> {
        value.as_array_mut()?.get_mut(*self)
    }
    fn get_or_insert<'v>(&self, value: &'v mut Value) -> &'v mut Value {
        value
            .as_array_mut()
            .expect("cannot index a non-array JSON value by position")
            .get_mut(*self)
            .expect("JSON array index is out of bounds")
    }
}
impl ValueIndex for str {
    fn get<'v>(&self, value: &'v Value) -> Option<&'v Value> {
        value.as_object()?.get(self)
    }
    fn get_mut<'v>(&self, value: &'v mut Value) -> Option<&'v mut Value> {
        value.as_object_mut()?.get_mut(self)
    }
    fn get_or_insert<'v>(&self, value: &'v mut Value) -> &'v mut Value {
        if value.is_null() {
            *value = Value::object(Map::new());
        }
        value
            .as_object_mut()
            .expect("cannot index a non-object JSON value by key")
            .entry(self.to_owned())
            .or_insert(Value::Null)
    }
}
impl ValueIndex for String {
    fn get<'v>(&self, value: &'v Value) -> Option<&'v Value> {
        <str as ValueIndex>::get(self.as_str(), value)
    }
    fn get_mut<'v>(&self, value: &'v mut Value) -> Option<&'v mut Value> {
        <str as ValueIndex>::get_mut(self.as_str(), value)
    }
    fn get_or_insert<'v>(&self, value: &'v mut Value) -> &'v mut Value {
        <str as ValueIndex>::get_or_insert(self.as_str(), value)
    }
}
impl<T: ValueIndex + ?Sized> ValueIndex for &T {
    fn get<'v>(&self, value: &'v Value) -> Option<&'v Value> {
        <T as ValueIndex>::get(*self, value)
    }
    fn get_mut<'v>(&self, value: &'v mut Value) -> Option<&'v mut Value> {
        <T as ValueIndex>::get_mut(*self, value)
    }
    fn get_or_insert<'v>(&self, value: &'v mut Value) -> &'v mut Value {
        <T as ValueIndex>::get_or_insert(*self, value)
    }
}
impl<I: ValueIndex> Index<I> for Value {
    type Output = Value;
    fn index(&self, index: I) -> &Value {
        static NULL: Value = Value::Null;
        index.get(self).unwrap_or(&NULL)
    }
}
impl<I: ValueIndex> IndexMut<I> for Value {
    fn index_mut(&mut self, index: I) -> &mut Value {
        index.get_or_insert(self)
    }
}

impl Serialize for Value {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        crate::payload_sharing::serialize_value(self, serializer)
    }
}
impl<'de> Deserialize<'de> for Value {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        RawValue::deserialize(deserializer).map(Self::from_raw)
    }
}

pub struct Plain<'a>(pub &'a Value);
impl Serialize for Plain<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self.0 {
            Value::Null => serializer.serialize_unit(),
            Value::Bool(value) => serializer.serialize_bool(*value),
            Value::Number(value) => value.serialize(serializer),
            Value::String(value) => serializer.serialize_str(value.as_str()),
            Value::Array(values) => {
                let mut seq = serializer.serialize_seq(Some(values.len()))?;
                for value in values {
                    seq.serialize_element(&Plain(value))?;
                }
                seq.end()
            }
            Value::Object(values) => {
                let mut map = serializer.serialize_map(Some(values.len()))?;
                for (key, value) in values {
                    map.serialize_entry(key, &Plain(value))?;
                }
                map.end()
            }
        }
    }
}
impl fmt::Display for Value {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = if formatter.alternate() {
            serde_json::to_string_pretty(&Plain(self))
        } else {
            serde_json::to_string(&Plain(self))
        }
        .map_err(|_| fmt::Error)?;
        formatter.write_str(&text)
    }
}

impl From<String> for Value {
    fn from(value: String) -> Self {
        Self::string(value)
    }
}
impl From<&str> for Value {
    fn from(value: &str) -> Self {
        Self::string(value.to_owned())
    }
}
impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Self::Bool(value)
    }
}
impl From<Number> for Value {
    fn from(value: Number) -> Self {
        Self::Number(value)
    }
}
impl From<Vec<Value>> for Value {
    fn from(value: Vec<Value>) -> Self {
        Self::array(value)
    }
}
impl From<Map> for Value {
    fn from(value: Map) -> Self {
        Self::object(value)
    }
}
macro_rules! integer_from {
    ($($ty:ty),*) => {$ (
        impl From<$ty> for Value { fn from(value: $ty) -> Self { Self::Number(Number::from(value)) } }
    )*};
}
integer_from!(i8, i16, i32, i64, isize, u8, u16, u32, u64, usize);
impl From<f32> for Value {
    fn from(value: f32) -> Self {
        Self::from(value as f64)
    }
}
impl From<f64> for Value {
    fn from(value: f64) -> Self {
        Number::from_f64(value)
            .map(Self::Number)
            .unwrap_or(Self::Null)
    }
}
impl PartialEq<str> for Value {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == Some(other)
    }
}
impl PartialEq<&str> for Value {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == Some(*other)
    }
}
impl PartialEq<String> for Value {
    fn eq(&self, other: &String) -> bool {
        self.as_str() == Some(other.as_str())
    }
}
impl PartialEq<bool> for Value {
    fn eq(&self, other: &bool) -> bool {
        self.as_bool() == Some(*other)
    }
}
macro_rules! integer_eq {
    ($method:ident, $($ty:ty),*) => {$ (
        impl PartialEq<$ty> for Value {
            fn eq(&self, other: &$ty) -> bool { self.$method().map(|v| v as i128) == Some(*other as i128) }
        }
    )*};
}
integer_eq!(as_i64, i8, i16, i32, i64, isize);
integer_eq!(as_u64, u8, u16, u32, u64, usize);

/// Serialize interpolated values as registry references, then recover their
/// canonical semantic handles while assembling this new literal's containers.
macro_rules! json {
    ($($json:tt)+) => {
        $crate::payload_value::Value::from_wire(::serde_json::json!($($json)+))
    };
}
pub(crate) use json;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clones_and_macro_interpolation_reuse_container_identity() {
        let child = json!({"values": [1, 2, 3], "name": "shared"});
        let clone = child.clone();
        assert_eq!(child.identity(), clone.identity());
        let parent = json!({"left": child, "right": clone});
        assert_eq!(parent["left"].identity(), parent["right"].identity());
        assert_eq!(parent["left"]["values"][1], 2);
    }

    #[test]
    fn nested_mutation_preserves_other_occurrences_and_cached_evidence() {
        let child = json!({"name": "original", "values": [1, 2]});
        let mut changed = json!({"children": [child.clone(), child.clone()]});
        let cached = changed.clone();
        changed["children"][0]["name"] = json!("changed");
        changed["children"][0]["values"][0] = json!(9);
        assert_eq!(cached["children"][0]["name"], "original");
        assert_eq!(cached["children"][0]["values"][0], 1);
        assert_eq!(changed["children"][1].identity(), child.identity());
        assert_eq!(changed["children"][0]["name"], "changed");
    }

    #[test]
    fn plain_serialization_and_deserialization_preserve_reserved_literal_objects() {
        let raw = serde_json::json!({"$lean_miri_shared_ref": 7, "values": [true, null, -1, 1.25]});
        let value = Value::from_raw(raw.clone());
        let plain = serde_json::to_value(Plain(&value)).unwrap();
        assert_eq!(plain, raw);
        let decoded: Value = serde_json::from_str(&raw.to_string()).unwrap();
        assert_eq!(serde_json::to_value(Plain(&decoded)).unwrap(), raw);
        assert_eq!(value.to_string(), raw.to_string());
    }

    #[test]
    fn pointers_and_container_iteration_match_json_values() {
        let mut value = json!({"a/b": {"~key": [3, 4]}});
        assert_eq!(value.pointer("/a~1b/~0key/1").unwrap(), &json!(4));
        assert!(value.pointer("/a~1b/~0key/01").is_none());
        *value.pointer_mut("/a~1b/~0key/0").unwrap() = json!(5);
        let Value::Array(mut values) = value["a/b"]["~key"].clone() else {
            panic!()
        };
        for child in &mut values {
            *child = json!(8);
        }
        let owned: Vec<_> = values.into_iter().collect();
        assert_eq!(owned, vec![json!(8), json!(8)]);
        assert_eq!(value["a/b"]["~key"][0], 5);
        assert_eq!(value["a/b"]["~key"][1], 4);
    }

    #[test]
    fn borrowed_indices_and_null_object_insertion_preserve_json_contract() {
        let key = String::from("field");
        let mut value = Value::Null;
        value[&key] = json!([7]);
        assert_eq!(value.get(&key).unwrap()[0], 7);
        *value.get_mut(&key).unwrap() = json!(true);
        assert_eq!(value["field"], true);
        assert!(value.get("absent").is_none());
        assert!(value["absent"].is_null());
        let Value::Object(fields) = value else {
            panic!()
        };
        let owned: Vec<_> = fields.into_iter().collect();
        assert_eq!(owned, vec![(key, json!(true))]);
    }
}
