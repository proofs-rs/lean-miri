//! Persistent construction graph. Cloning a compiler payload copies an Arc,
//! never its descendants. Mutation is copy-on-write and preserves the snapshot
//! semantics of serde_json::Value. Serialization is the external JSON boundary.
use serde::{Serialize, Serializer};
use std::collections::{BTreeMap, HashMap};
use std::hash::{BuildHasher, Hash};
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::sync::Arc;

pub type Map<K = String, V = Value> = BTreeMap<K, V>;

#[derive(Debug)]
pub struct Shared<T>(Arc<T>, std::sync::OnceLock<u64>);
impl<T> Clone for Shared<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), self.1.clone())
    }
}
impl<T: crate::construction_pool::Internable> From<T> for Shared<T> {
    fn from(value: T) -> Self {
        crate::construction_pool::intern(value)
    }
}
impl<T> Shared<T> {
    pub fn fresh(value: T, hash: Option<u64>) -> Self {
        let node = Self(Arc::new(value), std::sync::OnceLock::new());
        if let Some(hash) = hash {
            let _ = node.1.set(hash);
        }
        node
    }
    pub fn from_arc(value: Arc<T>, hash: u64) -> Self {
        let node = Self(value, std::sync::OnceLock::new());
        let _ = node.1.set(hash);
        node
    }
    pub fn identity_eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl<T: crate::construction_pool::Internable> Shared<T> {
    pub fn cached_digest(&self) -> u64 {
        *self.1.get_or_init(|| self.0.digest())
    }
}
impl<T: Default + crate::construction_pool::Internable> Default for Shared<T> {
    fn default() -> Self {
        T::default().into()
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
        self.1.take();
        Arc::make_mut(&mut self.0)
    }
}
impl<T: PartialEq> PartialEq for Shared<T> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || **self == **other
    }
}
impl<T: Eq> Eq for Shared<T> {}
impl<T: Clone + IntoIterator> IntoIterator for Shared<T> {
    type Item = T::Item;
    type IntoIter = T::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        Arc::unwrap_or_clone(self.0).into_iter()
    }
}
impl<'a, T> IntoIterator for &'a Shared<T>
where
    &'a T: IntoIterator,
{
    type Item = <&'a T as IntoIterator>::Item;
    type IntoIter = <&'a T as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        (&**self).into_iter()
    }
}
impl<'a, T: Clone> IntoIterator for &'a mut Shared<T>
where
    &'a mut T: IntoIterator,
{
    type Item = <&'a mut T as IntoIterator>::Item;
    type IntoIter = <&'a mut T as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        (&mut **self).into_iter()
    }
}
impl FromIterator<Value> for Shared<Vec<Value>> {
    fn from_iter<T: IntoIterator<Item = Value>>(items: T) -> Self {
        Vec::from_iter(items).into()
    }
}
impl FromIterator<(String, Value)> for Shared<Map> {
    fn from_iter<T: IntoIterator<Item = (String, Value)>>(items: T) -> Self {
        Map::from_iter(items).into()
    }
}

#[derive(Clone, Debug, PartialEq, Default)]
pub enum Value {
    #[default]
    Null,
    Bool(bool),
    Number(serde_json::Number),
    String(Shared<String>),
    Array(Shared<Vec<Value>>),
    Object(Shared<Map>),
}
impl Value {
    pub fn fingerprint(&self) -> u64 {
        crate::construction_pool::fingerprint(self)
    }
    pub fn array(values: Vec<Self>) -> Self {
        Self::Array(values.into())
    }
    pub fn object(values: Map) -> Self {
        Self::Object(values.into())
    }
    pub fn is_null(&self) -> bool {
        matches!(self, Self::Null)
    }
    pub fn is_boolean(&self) -> bool {
        matches!(self, Self::Bool(_))
    }
    pub fn is_number(&self) -> bool {
        matches!(self, Self::Number(_))
    }
    pub fn is_string(&self) -> bool {
        matches!(self, Self::String(_))
    }
    pub fn is_array(&self) -> bool {
        matches!(self, Self::Array(_))
    }
    pub fn as_bool(&self) -> Option<bool> {
        if let Self::Bool(v) = self {
            Some(*v)
        } else {
            None
        }
    }
    pub fn as_u64(&self) -> Option<u64> {
        if let Self::Number(v) = self {
            v.as_u64()
        } else {
            None
        }
    }
    pub fn as_i64(&self) -> Option<i64> {
        if let Self::Number(v) = self {
            v.as_i64()
        } else {
            None
        }
    }
    pub fn as_f64(&self) -> Option<f64> {
        if let Self::Number(v) = self {
            v.as_f64()
        } else {
            None
        }
    }
    pub fn as_str(&self) -> Option<&str> {
        if let Self::String(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn as_array(&self) -> Option<&Vec<Self>> {
        if let Self::Array(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn as_array_mut(&mut self) -> Option<&mut Vec<Self>> {
        if let Self::Array(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn as_object(&self) -> Option<&Map> {
        if let Self::Object(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn as_object_mut(&mut self) -> Option<&mut Map> {
        if let Self::Object(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub fn get(&self, key: &str) -> Option<&Self> {
        self.as_object()?.get(key)
    }
    pub fn get_mut(&mut self, key: &str) -> Option<&mut Self> {
        self.as_object_mut()?.get_mut(key)
    }
    pub fn pointer(&self, pointer: &str) -> Option<&Self> {
        if pointer.is_empty() {
            return Some(self);
        }
        let mut value = self;
        for token in pointer.strip_prefix('/')?.split('/') {
            let token = token.replace("~1", "/").replace("~0", "~");
            value = match value {
                Self::Object(fields) => fields.get(&token)?,
                Self::Array(values) => {
                    if token.starts_with('+') || (token.len() > 1 && token.starts_with('0')) {
                        return None;
                    }
                    values.get(token.parse::<usize>().ok()?)?
                }
                _ => return None,
            };
        }
        Some(value)
    }
    /// Unique nodes need no traversal memo or retained snapshot.
    pub fn is_shared(&self) -> bool {
        match self {
            Self::String(v) => Arc::strong_count(&v.0) > 1,
            Self::Array(v) => Arc::strong_count(&v.0) > 1,
            Self::Object(v) => Arc::strong_count(&v.0) > 1,
            _ => false,
        }
    }
    /// Identity is used only while a clone retains the original immutable node.
    pub fn identity(&self) -> Option<(u8, usize)> {
        match self {
            Self::String(v) => Some((0, Arc::as_ptr(&v.0) as usize)),
            Self::Array(v) => Some((1, Arc::as_ptr(&v.0) as usize)),
            Self::Object(v) => Some((2, Arc::as_ptr(&v.0) as usize)),
            _ => None,
        }
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
impl PartialEq<bool> for Value {
    fn eq(&self, other: &bool) -> bool {
        self.as_bool() == Some(*other)
    }
}
macro_rules! compare_numbers {($method:ident,$target:ty,$($t:ty),*)=>{$(
    impl PartialEq<$t> for Value { fn eq(&self,other:&$t)->bool { self.$method()==Some(*other as $target) } }
)*};}
compare_numbers!(as_u64, u64, u8, u16, u32, u64, usize);
compare_numbers!(as_i64, i64, i8, i16, i32, i64, isize);
compare_numbers!(as_f64, f64, f32, f64);

/// Apply a context-independent metadata patch once per immutable construction
/// node. Unchanged edges keep their original Arc; no whole-tree COW traversal.
pub fn transform(root: &Value, patch: &impl Fn(&Value) -> Option<Value>) -> Value {
    fn visit(
        value: &Value,
        patch: &impl Fn(&Value) -> Option<Value>,
        memo: &mut HashMap<(u8, usize), (Value, Value)>,
    ) -> Value {
        let id = value.identity().filter(|_| value.is_shared());
        if let Some(id) = id {
            if let Some((_, result)) = memo.get(&id) {
                return result.clone();
            }
        }
        let mut result = patch(value).unwrap_or_else(|| value.clone());
        match &result {
            Value::Array(values) => {
                let mut changed = None;
                for (index, child) in values.iter().enumerate() {
                    let next = visit(child, patch, memo);
                    if !same_node(child, &next) {
                        let copy = changed.get_or_insert_with(|| values.clone());
                        copy[index] = next;
                    }
                }
                if let Some(values) = changed {
                    result = Value::Array(values);
                }
            }
            Value::Object(fields) => {
                let mut changed = None;
                for (key, child) in fields.iter() {
                    let next = visit(child, patch, memo);
                    if !same_node(child, &next) {
                        let copy = changed.get_or_insert_with(|| fields.clone());
                        copy.insert(key.clone(), next);
                    }
                }
                if let Some(fields) = changed {
                    result = Value::Object(fields);
                }
            }
            _ => (),
        }
        if let Some(id) = id {
            memo.insert(id, (value.clone(), result.clone()));
        }
        result
    }
    visit(root, patch, &mut HashMap::new())
}
fn same_node(a: &Value, b: &Value) -> bool {
    match (a.identity(), b.identity()) {
        (Some(a), Some(b)) => a == b,
        (None, None) => a == b,
        _ => false,
    }
}
impl Index<&str> for Value {
    type Output = Self;
    fn index(&self, key: &str) -> &Self {
        self.get(key).unwrap_or(&Self::Null)
    }
}
impl IndexMut<&str> for Value {
    fn index_mut(&mut self, key: &str) -> &mut Self {
        if self.is_null() {
            *self = Self::object(Map::new());
        }
        self.as_object_mut()
            .expect("JSON index requires object")
            .entry(key.into())
            .or_default()
    }
}
impl Index<usize> for Value {
    type Output = Self;
    fn index(&self, key: usize) -> &Self {
        self.as_array()
            .and_then(|v| v.get(key))
            .unwrap_or(&Self::Null)
    }
}
impl IndexMut<usize> for Value {
    fn index_mut(&mut self, key: usize) -> &mut Self {
        &mut self.as_array_mut().expect("JSON index requires array")[key]
    }
}
impl Serialize for Value {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Null => s.serialize_unit(),
            Self::Bool(v) => v.serialize(s),
            Self::Number(v) => v.serialize(s),
            Self::String(v) => (**v).serialize(s),
            Self::Array(v) => (**v).serialize(s),
            Self::Object(v) => (**v).serialize(s),
        }
    }
}
impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&serde_json::to_string(self).map_err(|_| std::fmt::Error)?)
    }
}
impl From<serde_json::Value> for Value {
    fn from(v: serde_json::Value) -> Self {
        match v {
            serde_json::Value::Null => Self::Null,
            serde_json::Value::Bool(v) => Self::Bool(v),
            serde_json::Value::Number(v) => Self::Number(v),
            serde_json::Value::String(v) => Self::String(v.into()),
            serde_json::Value::Array(v) => Self::array(v.into_iter().map(Self::from).collect()),
            serde_json::Value::Object(v) => {
                Self::object(v.into_iter().map(|(k, v)| (k, Self::from(v))).collect())
            }
        }
    }
}

pub trait IntoValue {
    fn into_value(&self) -> Value;
}
impl IntoValue for Value {
    fn into_value(&self) -> Value {
        self.clone()
    }
}
impl<T: IntoValue + ?Sized> IntoValue for &T {
    fn into_value(&self) -> Value {
        (**self).into_value()
    }
}
impl IntoValue for str {
    fn into_value(&self) -> Value {
        Value::String(self.to_owned().into())
    }
}
impl IntoValue for std::borrow::Cow<'_, str> {
    fn into_value(&self) -> Value {
        self.as_ref().into_value()
    }
}
impl IntoValue for String {
    fn into_value(&self) -> Value {
        self.as_str().into_value()
    }
}
impl<T: IntoValue> IntoValue for Option<T> {
    fn into_value(&self) -> Value {
        self.as_ref()
            .map(IntoValue::into_value)
            .unwrap_or(Value::Null)
    }
}
impl<T: IntoValue> IntoValue for [T] {
    fn into_value(&self) -> Value {
        Value::array(self.iter().map(IntoValue::into_value).collect())
    }
}
impl<T: IntoValue> IntoValue for Vec<T> {
    fn into_value(&self) -> Value {
        self.as_slice().into_value()
    }
}
impl<T: IntoValue, const N: usize> IntoValue for [T; N] {
    fn into_value(&self) -> Value {
        self.as_slice().into_value()
    }
}
impl<A: IntoValue, B: IntoValue> IntoValue for (A, B) {
    fn into_value(&self) -> Value {
        Value::array(vec![self.0.into_value(), self.1.into_value()])
    }
}
impl<A: IntoValue, B: IntoValue, C: IntoValue> IntoValue for (A, B, C) {
    fn into_value(&self) -> Value {
        Value::array(vec![
            self.0.into_value(),
            self.1.into_value(),
            self.2.into_value(),
        ])
    }
}
impl<K: AsRef<str> + Ord, V: IntoValue> IntoValue for BTreeMap<K, V> {
    fn into_value(&self) -> Value {
        Value::object(
            self.iter()
                .map(|(k, v)| (k.as_ref().into(), v.into_value()))
                .collect(),
        )
    }
}
impl<K: AsRef<str> + Eq + Hash, V: IntoValue, S: BuildHasher> IntoValue for HashMap<K, V, S> {
    fn into_value(&self) -> Value {
        Value::object(
            self.iter()
                .map(|(k, v)| (k.as_ref().into(), v.into_value()))
                .collect(),
        )
    }
}
macro_rules! primitives {($($t:ty),*)=>{$(impl IntoValue for $t {
    fn into_value(&self)->Value { serde_json::to_value(self).unwrap().into() }
})*};}
primitives!(
    bool,
    u8,
    u16,
    u32,
    u64,
    u128,
    usize,
    i8,
    i16,
    i32,
    i64,
    i128,
    isize,
    f32,
    f64,
    char,
    serde_json::Number
);

pub struct Expression<'a, T: ?Sized>(pub &'a T);
pub trait Convert {
    fn convert(self) -> Value;
}
impl<T: IntoValue + ?Sized> Convert for Expression<'_, T> {
    fn convert(self) -> Value {
        self.0.into_value()
    }
}
// Deliberately no arbitrary Serialize fallback: adding a new expression must
// provide an explicit construction conversion, never silently expand a payload
// graph through serde_json::to_value.

#[path = "shared_json_macro.rs"]
mod macros;
pub(crate) use crate::shared_json as json;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn macro_preserves_serde_values_and_cow_snapshots() {
        let input = json!({"nested":[{"a":1,"b":"text"}],"null":null,"bool":true});
        let expected = serde_json::json!({"nested":[{"a":1,"b":"text"}],"null":null,"bool":true});
        assert_eq!(input.to_string(), expected.to_string());
        let values = vec![input.clone(), input.clone()];
        let wrapped =
            json!({"values":values,"optional":Some(input.clone()),"pair":(input.clone(),7)});
        assert_eq!(wrapped["values"][0].identity(), input.identity());
        assert_eq!(wrapped["optional"].identity(), input.identity());
        assert_eq!(wrapped["pair"][0].identity(), input.identity());
        let mut copy = input.clone();
        copy["nested"][0]["a"] = json!(2);
        assert_eq!(input.to_string(), expected.to_string());
        assert_eq!(copy["nested"][0]["a"], json!(2));
        assert_eq!(copy.pointer("/nested/0/a"), Some(&json!(2)));
    }

    #[test]
    fn repeated_payload_construction_stays_a_dag() {
        let mut value = json!({"leaf":"data"});
        for _ in 0..40 {
            value = json!({"left":value,"right":value});
        }
        let mut ids = std::collections::HashSet::new();
        fn count(v: &Value, ids: &mut std::collections::HashSet<(u8, usize)>) {
            if let Some(id) = v.identity() {
                if !ids.insert(id) {
                    return;
                }
            }
            match v {
                Value::Array(a) => {
                    for c in a.iter() {
                        count(c, ids)
                    }
                }
                Value::Object(o) => {
                    for c in o.values() {
                        count(c, ids)
                    }
                }
                _ => (),
            }
        }
        count(&value, &mut ids);
        assert!(ids.len() < 50, "construction expanded shared descendants");
        let mut document = json!({"root":value});
        crate::payload_sharing::share_payloads(&mut document).unwrap();
        assert!(
            document["shared_payloads"]["nodes"]
                .as_array()
                .unwrap()
                .len()
                < 50
        );
        assert!(document.to_string().len() < 10_000);
    }

    #[test]
    fn persistent_transform_retains_aliases_and_originals() {
        let leaf = json!({"patch":true,"value":7});
        let root = json!({"left":leaf,"right":leaf});
        let changed = transform(&root, &|v| {
            if v.get("patch").and_then(Value::as_bool) != Some(true) {
                return None;
            }
            let mut next = v.clone();
            next["value"] = json!(8);
            Some(next)
        });
        assert_eq!(root["left"]["value"], json!(7));
        assert_eq!(changed["left"]["value"], json!(8));
        assert_eq!(changed["left"].identity(), changed["right"].identity());
        assert_eq!(transform(&root, &|_| None).identity(), root.identity());
    }
}
