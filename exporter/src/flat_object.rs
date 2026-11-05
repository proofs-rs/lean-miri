//! Ordered fields for small construction objects. Keep one compact allocation
//! instead of a BTree node sized for many fields. Mutations preserve key order
//! and duplicate insertion keeps the last value, matching serde_json::Map.
use super::Value;
use serde::{Serialize, Serializer, ser::SerializeMap};
use std::borrow::{Borrow, Cow};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FieldName(Cow<'static, str>);
impl FieldName {
    pub fn as_str(&self) -> &str {
        &self.0
    }
}
impl From<&'static str> for FieldName {
    fn from(s: &'static str) -> Self {
        Self(Cow::Borrowed(s))
    }
}
impl From<String> for FieldName {
    fn from(s: String) -> Self {
        Self(Cow::Owned(s))
    }
}
impl Borrow<str> for FieldName {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}
impl AsRef<str> for FieldName {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}
impl std::ops::Deref for FieldName {
    type Target = str;
    fn deref(&self) -> &str {
        self.as_str()
    }
}
impl PartialEq<str> for FieldName {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}
impl PartialEq<&str> for FieldName {
    fn eq(&self, other: &&str) -> bool {
        self.as_str() == *other
    }
}
impl Serialize for FieldName {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(self.as_str())
    }
}
impl std::fmt::Display for FieldName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Map<K = FieldName, V = Value>(Vec<(K, V)>);
impl<K, V> Default for Map<K, V> {
    fn default() -> Self {
        Self(Vec::new())
    }
}
impl<K, V> Map<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = (&K, &V)> + ExactSizeIterator {
        self.0.iter().map(|(k, v)| (k, v))
    }
    pub fn iter_mut(
        &mut self,
    ) -> impl DoubleEndedIterator<Item = (&K, &mut V)> + ExactSizeIterator {
        self.0.iter_mut().map(|(k, v)| (&*k, v))
    }
    pub fn keys(&self) -> impl DoubleEndedIterator<Item = &K> + ExactSizeIterator {
        self.0.iter().map(|(k, _)| k)
    }
    pub fn values(&self) -> impl DoubleEndedIterator<Item = &V> + ExactSizeIterator {
        self.0.iter().map(|(_, v)| v)
    }
    pub fn values_mut(&mut self) -> impl DoubleEndedIterator<Item = &mut V> + ExactSizeIterator {
        self.0.iter_mut().map(|(_, v)| v)
    }
}
impl<K: Ord, V> Map<K, V> {
    fn position<Q: Ord + ?Sized>(&self, key: &Q) -> Result<usize, usize>
    where
        K: Borrow<Q>,
    {
        self.0.binary_search_by(|(k, _)| k.borrow().cmp(key))
    }
    pub fn get<Q: Ord + ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
    {
        self.position(key).ok().map(|i| &self.0[i].1)
    }
    pub fn get_mut<Q: Ord + ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
    {
        self.position(key).ok().map(|i| &mut self.0[i].1)
    }
    pub fn contains_key<Q: Ord + ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
    {
        self.position(key).is_ok()
    }
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.position(&key) {
            Ok(i) => Some(std::mem::replace(&mut self.0[i].1, value)),
            Err(i) => {
                self.0.insert(i, (key, value));
                None
            }
        }
    }
    pub fn remove<Q: Ord + ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
    {
        self.position(key).ok().map(|i| self.0.remove(i).1)
    }
    pub fn get_mut_or_insert_default(&mut self, key: K) -> &mut V
    where
        V: Default,
    {
        let i = match self.position(&key) {
            Ok(i) => i,
            Err(i) => {
                self.0.insert(i, (key, V::default()));
                i
            }
        };
        &mut self.0[i].1
    }
}
impl<K: Ord + Borrow<Q>, Q: Ord + ?Sized, V> std::ops::Index<&Q> for Map<K, V> {
    type Output = V;
    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("missing object field")
    }
}
impl<K: Ord, V> FromIterator<(K, V)> for Map<K, V> {
    fn from_iter<I: IntoIterator<Item = (K, V)>>(input: I) -> Self {
        let mut result = Self::new();
        for (k, v) in input {
            result.insert(k, v);
        }
        result
    }
}
impl<K: Ord, V> Extend<(K, V)> for Map<K, V> {
    fn extend<I: IntoIterator<Item = (K, V)>>(&mut self, input: I) {
        for (k, v) in input {
            self.insert(k, v);
        }
    }
}
impl<K, V> IntoIterator for Map<K, V> {
    type Item = (K, V);
    type IntoIter = std::vec::IntoIter<(K, V)>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}
fn refs<K, V>((k, v): &(K, V)) -> (&K, &V) {
    (k, v)
}
fn refs_mut<K, V>((k, v): &mut (K, V)) -> (&K, &mut V) {
    (&*k, v)
}
impl<'a, K, V> IntoIterator for &'a Map<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = std::iter::Map<std::slice::Iter<'a, (K, V)>, fn(&'a (K, V)) -> (&'a K, &'a V)>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().map(refs::<K, V>)
    }
}
impl<'a, K, V> IntoIterator for &'a mut Map<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter =
        std::iter::Map<std::slice::IterMut<'a, (K, V)>, fn(&'a mut (K, V)) -> (&'a K, &'a mut V)>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut().map(refs_mut::<K, V>)
    }
}
impl<K: Serialize, V: Serialize> Serialize for Map<K, V> {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let mut out = s.serialize_map(Some(self.len()))?;
        for (k, v) in self {
            out.serialize_entry(k, v)?;
        }
        out.end()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;
    #[test]
    fn borrowed_and_owned_names_are_the_same_ordered_key() {
        let mut fields: Map<FieldName, u32> = Map::new();
        fields.insert("z".into(), 1);
        fields.insert("a".to_owned().into(), 2);
        assert_eq!(fields.insert("z".to_owned().into(), 3), Some(1));
        assert_eq!(fields.insert("a".into(), 4), Some(2));
        assert_eq!(serde_json::to_string(&fields).unwrap(), r#"{"a":4,"z":3}"#);
        assert_eq!(fields.get("z"), Some(&3));
        assert_eq!(fields.remove("a"), Some(4));
    }

    #[test]
    fn mutations_and_duplicate_keys_match_ordered_reference_map() {
        for count in [0, 1, 2, 7, 11, 12, 40, 100] {
            let mut actual = Map::new();
            let mut expected = BTreeMap::new();
            for index in (0..count * 3).rev() {
                let key = format!("field-{:03}", index % count.max(1));
                assert_eq!(
                    actual.insert(key.clone(), index),
                    expected.insert(key, index)
                );
            }
            let snapshot = actual.clone();
            for index in 0..count {
                let key = format!("field-{index:03}");
                assert_eq!(actual.get(key.as_str()), expected.get(key.as_str()));
                if index % 2 == 0 {
                    assert_eq!(actual.remove(key.as_str()), expected.remove(key.as_str()));
                }
            }
            for value in actual.values_mut() {
                *value += 1;
            }
            for value in expected.values_mut() {
                *value += 1;
            }
            assert_eq!(
                serde_json::to_string(&actual).unwrap(),
                serde_json::to_string(&expected).unwrap()
            );
            assert_eq!(snapshot.len(), count);
        }
        let actual: Map<_, _> = [("b", 1), ("a", 2), ("b", 3)].into_iter().collect();
        assert_eq!(serde_json::to_string(&actual).unwrap(), r#"{"a":2,"b":3}"#);
    }
}
