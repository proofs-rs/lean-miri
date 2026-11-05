//! Occurrence-sensitive diagnostics over the immutable construction graph.
//! Cache relative results, including empty branches, then rebase every hit at
//! each occurrence. Repeated diagnostics and their traversal order survive.
use crate::Value;
use std::collections::HashMap;
use std::rc::Rc;

type Hits = Option<Rc<Vec<(String, Value)>>>;

pub struct Collector<F> {
    classify: F,
    // Retaining the source prevents reuse of its address while cached.
    memo: HashMap<(u8, usize), (Value, Hits)>,
}
impl<F: Fn(&Value) -> Option<Vec<(String, Value)>>> Collector<F> {
    pub fn new(classify: F) -> Self {
        Self {
            classify,
            memo: HashMap::new(),
        }
    }
    fn visit(&mut self, value: &Value) -> Hits {
        if !matches!(value, Value::Array(_) | Value::Object(_)) {
            return None;
        }
        #[cfg(not(feature = "legacy-json"))]
        let identity = value.identity().filter(|_| value.is_shared());
        #[cfg(feature = "legacy-json")]
        let identity: Option<(u8, usize)> = None;
        if let Some(identity) = identity {
            if let Some((_, hits)) = self.memo.get(&identity) {
                return hits.clone();
            }
        }
        let hits = (self.classify)(value).and_then(|mut hits| {
            match value {
                Value::Array(values) => {
                    for (index, child) in values.iter().enumerate() {
                        // No path is constructed for a branch with no diagnostics.
                        if let Some(children) = self.visit(child) {
                            for (path, payload) in children.iter() {
                                hits.push((format!("[{index}]{path}"), payload.clone()));
                            }
                        }
                    }
                }
                Value::Object(fields) => {
                    for (key, child) in fields {
                        // Deliberately preserve the historical unescaped producer paths.
                        if let Some(children) = self.visit(child) {
                            for (path, payload) in children.iter() {
                                hits.push((format!(".{key}{path}"), payload.clone()));
                            }
                        }
                    }
                }
                _ => unreachable!(),
            }
            if hits.is_empty() {
                None
            } else {
                Some(Rc::new(hits))
            }
        });
        if let Some(identity) = identity {
            self.memo.insert(identity, (value.clone(), hits.clone()));
        }
        hits
    }
    pub fn collect(&mut self, value: &Value, root: &str, out: &mut Vec<Value>) {
        if let Some(hits) = self.visit(value) {
            for (path, payload) in hits.iter() {
                let mut row = payload.clone();
                row["path"] = crate::json!(format!("{root}{path}"));
                out.push(row);
            }
        }
    }
}
