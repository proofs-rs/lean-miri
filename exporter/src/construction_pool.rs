//! Compilation-thread-local canonical immutable construction nodes.
//! Hashes select buckets only; complete wire equality resolves collisions.
use crate::shared_value::{Map, Shared, Value};
use rustc_data_structures::fx::{FxHashMap, FxHasher};
use std::cell::RefCell;
use std::hash::{Hash, Hasher};
use std::rc::{Rc, Weak};

#[derive(Default)]
pub struct Pool {
    strings: FxHashMap<u64, Vec<Weak<String>>>,
    arrays: FxHashMap<u64, Vec<Weak<Vec<Value>>>>,
    objects: FxHashMap<u64, Vec<Weak<Map>>>,
}
thread_local! {
    static ENABLED: std::cell::Cell<bool> = std::cell::Cell::new(
        std::env::var_os("LEAN_MIRI_PREPARED_IMAGE").is_none_or(|value| value=="1"));
    static POOL: RefCell<Pool> = RefCell::new(Pool::default());
}
pub fn enabled() -> bool {
    ENABLED.with(|v| v.get())
}

pub trait Internable: Sized {
    fn digest(&self) -> u64;
    fn exact(&self, other: &Self) -> bool;
    fn buckets(pool: &mut Pool) -> &mut FxHashMap<u64, Vec<Weak<Self>>>;
}
fn digest(tag: u8, action: impl FnOnce(&mut FxHasher)) -> u64 {
    let mut h = FxHasher::default();
    tag.hash(&mut h);
    action(&mut h);
    h.finish()
}
impl Internable for String {
    fn digest(&self) -> u64 {
        digest(4, |h| self.hash(h))
    }
    fn exact(&self, other: &Self) -> bool {
        self == other
    }
    fn buckets(pool: &mut Pool) -> &mut FxHashMap<u64, Vec<Weak<Self>>> {
        &mut pool.strings
    }
}
impl Internable for Vec<Value> {
    fn digest(&self) -> u64 {
        digest(5, |h| {
            self.len().hash(h);
            for v in self {
                v.fingerprint().hash(h);
            }
        })
    }
    fn exact(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().zip(other).all(|(a, b)| exact(a, b))
    }
    fn buckets(pool: &mut Pool) -> &mut FxHashMap<u64, Vec<Weak<Self>>> {
        &mut pool.arrays
    }
}
impl Internable for Map {
    fn digest(&self) -> u64 {
        digest(6, |h| {
            self.len().hash(h);
            for (k, v) in self {
                k.hash(h);
                v.fingerprint().hash(h);
            }
        })
    }
    fn exact(&self, other: &Self) -> bool {
        self.len() == other.len()
            && self
                .iter()
                .zip(other)
                .all(|((a, x), (b, y))| a == b && exact(x, y))
    }
    fn buckets(pool: &mut Pool) -> &mut FxHashMap<u64, Vec<Weak<Self>>> {
        &mut pool.objects
    }
}
pub fn intern<T: Internable>(value: T) -> Shared<T> {
    if !enabled() {
        return Shared::fresh(value, None);
    }
    let hash = value.digest();
    intern_at_hash(value, hash)
}
/// Most scalar strings are repeated protocol tags. Check the existing string
/// bucket before allocating an owned candidate; misses retain their own copy.
pub fn intern_str(value: &str) -> Shared<String> {
    if !enabled() {
        return Shared::fresh(value.to_owned(), None);
    }
    let hash = digest(4, |h| value.hash(h));
    POOL.with(|pool| {
        let mut pool = pool.borrow_mut();
        let bucket = pool.strings.entry(hash).or_default();
        let mut found = None;
        bucket.retain(|weak| {
            if let Some(old) = weak.upgrade() {
                if old.as_str() == value {
                    found = Some(old);
                }
                true
            } else {
                false
            }
        });
        let node = found.unwrap_or_else(|| {
            let node = Rc::new(value.to_owned());
            bucket.push(Rc::downgrade(&node));
            node
        });
        Shared::from_rc(node, hash)
    })
}
fn intern_at_hash<T: Internable>(value: T, hash: u64) -> Shared<T> {
    POOL.with(|pool| {
        let mut pool = pool.borrow_mut();
        let bucket = T::buckets(&mut pool).entry(hash).or_default();
        let mut found = None;
        bucket.retain(|weak| {
            if let Some(old) = weak.upgrade() {
                if old.exact(&value) {
                    found = Some(old);
                }
                true
            } else {
                false
            }
        });
        let node = found.unwrap_or_else(|| {
            let node = Rc::new(value);
            bucket.push(Rc::downgrade(&node));
            node
        });
        Shared::from_rc(node, hash)
    })
}
pub fn exact(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Null, Value::Null) => true,
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Number(a), Value::Number(b)) => match (a.as_u64(), b.as_u64()) {
            (Some(a), Some(b)) => a == b,
            _ => match (a.as_i64(), b.as_i64()) {
                (Some(a), Some(b)) => a == b,
                // Preserve floating-point spelling, including negative zero.
                _ => a.to_string() == b.to_string(),
            },
        },
        (Value::String(a), Value::String(b)) => a.identity_eq(b) || a.as_str() == b.as_str(),
        (Value::Array(a), Value::Array(b)) => a.identity_eq(b) || a.exact(b),
        (Value::Object(a), Value::Object(b)) => a.identity_eq(b) || a.exact(b),
        _ => false,
    }
}
pub fn fingerprint(v: &Value) -> u64 {
    match v {
        Value::Null => digest(0, |_| ()),
        Value::Bool(v) => digest(1, |h| v.hash(h)),
        Value::Number(v) => digest(3, |h| {
            if let Some(n) = v.as_u64() {
                0u8.hash(h);
                n.hash(h)
            } else if let Some(n) = v.as_i64() {
                1u8.hash(h);
                n.hash(h)
            } else {
                2u8.hash(h);
                v.to_string().hash(h)
            }
        }),
        Value::String(v) => v.cached_digest(),
        Value::Array(v) => v.cached_digest(),
        Value::Object(v) => v.cached_digest(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::json;
    #[test]
    fn borrowed_and_owned_strings_share_until_copy_on_write() {
        let previous = ENABLED.with(|v| v.replace(true));
        let borrowed = intern_str("borrowed-string-test");
        let owned = intern("borrowed-string-test".to_owned());
        assert!(borrowed.identity_eq(&owned));
        let mut changed = borrowed.clone();
        changed.push('!');
        assert_eq!(borrowed.as_str(), "borrowed-string-test");
        assert_eq!(changed.as_str(), "borrowed-string-test!");
        assert!(owned.identity_eq(&intern_str("borrowed-string-test")));
        ENABLED.with(|v| v.set(previous));
    }

    #[test]
    fn numeric_equality_matches_exact_wire_spelling() {
        let values = [
            "0",
            "-0",
            "0.0",
            "-0.0",
            "1",
            "1.0",
            "1e0",
            "-1",
            "18446744073709551615",
            "-9223372036854775808",
            "9007199254740993",
            "1.0000000000000002",
            "1e-100",
            "1e100",
        ]
        .map(|text| Value::from(serde_json::from_str::<serde_json::Value>(text).unwrap()));
        for a in &values {
            for b in &values {
                assert_eq!(exact(a, b), a.to_string() == b.to_string());
            }
        }
        let negative = intern_at_hash(Map::from_iter([("n".into(), json!(-0.0))]), 9);
        let positive = intern_at_hash(Map::from_iter([("n".into(), json!(0.0))]), 9);
        assert!(!negative.identity_eq(&positive));
    }
    #[test]
    fn forced_collisions_keep_distinct_values() {
        POOL.with(|p| *p.borrow_mut() = Pool::default());
        let a = intern_at_hash("a".to_owned(), 7);
        let b = intern_at_hash("b".to_owned(), 7);
        let again = intern_at_hash("a".to_owned(), 7);
        assert!(!a.identity_eq(&b));
        assert!(a.identity_eq(&again));
    }
    #[test]
    fn canonical_snapshots_keep_mutations_and_numeric_spelling_distinct() {
        let previous = ENABLED.with(|v| v.replace(true));
        POOL.with(|p| *p.borrow_mut() = Pool::default());
        let original = json!({"type_id":17,"nested":[1,2]});
        let duplicate = json!({"type_id":17,"nested":[1,2]});
        assert_eq!(original.identity(), duplicate.identity());
        let fingerprint = original.fingerprint();
        let mut changed = original.clone();
        changed["nested"][0] = json!(9);
        assert_eq!(original["nested"][0], 1);
        assert_ne!(changed.fingerprint(), fingerprint);
        assert_eq!(original.fingerprint(), fingerprint);
        let negative = json!({"n":-0.0});
        let zero = json!({"n":0.0});
        let float = json!({"n":1.0});
        let integer = json!({"n":1});
        assert_ne!(negative.identity(), zero.identity());
        assert_ne!(float.identity(), integer.identity());
        ENABLED.with(|v| v.set(previous));
    }
}
