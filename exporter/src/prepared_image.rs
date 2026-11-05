//! Indexed execution graph: typed rows and field IDs, no final structural interner.
//! Construction nodes are already canonical; wire IDs describe representation,
//! never Rust type/allocation/instance identity.
use crate::Value;
#[cfg(test)]
use crate::json;
use serde::{
    Serialize, Serializer,
    ser::{SerializeStruct, SerializeTuple},
};
use std::collections::HashMap;

/// The output table is typed Rust data, serialized straight to the writer.
/// It never becomes a second generic JSON Value tree.
#[derive(Clone)]
pub struct Image {
    pub(crate) fields: Vec<String>,
    pub(crate) nodes: Vec<Row>,
    pub(crate) root: usize,
}
#[derive(Clone)]
pub(crate) enum Row {
    Empty(u8),
    Leaf(u8, Value),
    Array(Vec<usize>),
    Object(Vec<(usize, usize)>),
}
impl Serialize for Row {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut tuple =
            serializer.serialize_tuple(if matches!(self, Self::Empty(_)) { 1 } else { 2 })?;
        match self {
            Self::Empty(tag) => tuple.serialize_element(tag)?,
            Self::Leaf(tag, value) => {
                tuple.serialize_element(tag)?;
                tuple.serialize_element(value)?;
            }
            Self::Array(ids) => {
                tuple.serialize_element(&5u8)?;
                tuple.serialize_element(ids)?;
            }
            Self::Object(pairs) => {
                tuple.serialize_element(&6u8)?;
                tuple.serialize_element(pairs)?;
            }
        }
        tuple.end()
    }
}
impl Serialize for Image {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        // Match the canonical dictionary order of the reference JSON encoder.
        let mut record = serializer.serialize_struct("PreparedImage", 5)?;
        record.serialize_field("fields", &self.fields)?;
        record.serialize_field("nodes", &self.nodes)?;
        record.serialize_field("root", &self.root)?;
        record.serialize_field("schema", "lean-miri-prepared-image")?;
        record.serialize_field("schema_version", &1u8)?;
        record.end()
    }
}
#[cfg(test)]
fn wire(image: Image) -> Value {
    let direct = serde_json::to_string(&image).unwrap();
    let generic: Value = serde_json::to_value(image).unwrap().into();
    assert_eq!(
        direct,
        generic.to_string(),
        "typed writer changed canonical wire bytes"
    );
    generic
}

#[derive(Default)]
struct Encoder {
    nodes: Vec<Row>,
    fields: Vec<String>,
    field_ids: HashMap<String, usize>,
    identities: HashMap<(u8, usize), usize>,
    scalars: HashMap<String, usize>,
}
impl Encoder {
    fn field(&mut self, name: &str) -> usize {
        if let Some(id) = self.field_ids.get(name) {
            return *id;
        }
        let id = self.fields.len();
        self.fields.push(name.to_owned());
        self.field_ids.insert(name.to_owned(), id);
        id
    }
    fn visit(&mut self, value: &Value) -> Result<usize, String> {
        if let Some(identity) = value.identity() {
            if let Some(id) = self.identities.get(&identity) {
                return Ok(*id);
            }
        }
        let scalar = if value.identity().is_none() {
            Some(value.to_string())
        } else {
            None
        };
        if let Some(key) = &scalar {
            if let Some(id) = self.scalars.get(key) {
                return Ok(*id);
            }
        }
        let row = match value {
            Value::Null => Row::Empty(0),
            Value::Bool(false) => Row::Empty(1),
            Value::Bool(true) => Row::Empty(2),
            Value::Number(_) => Row::Leaf(3, value.clone()),
            Value::String(_) => Row::Leaf(4, value.clone()),
            Value::Array(values) => {
                let mut children = Vec::with_capacity(values.len());
                for child in values.iter() {
                    children.push(self.visit(child)?);
                }
                Row::Array(children)
            }
            Value::Object(fields) => {
                if fields.contains_key("$lean_miri_shared_ref") {
                    return Err("prepared input contains reserved shared reference marker".into());
                }
                let mut children = Vec::with_capacity(fields.len());
                for (name, child) in fields.iter() {
                    let field = self.field(name);
                    let id = self.visit(child)?;
                    children.push((field, id));
                }
                Row::Object(children)
            }
        };
        let id = self.nodes.len();
        self.nodes.push(row);
        if let Some(identity) = value.identity() {
            self.identities.insert(identity, id);
        }
        if let Some(key) = scalar {
            self.scalars.insert(key, id);
        }
        Ok(id)
    }
}
pub fn encode(document: &Value) -> Result<Image, String> {
    let Some(root) = document.as_object() else {
        return Err("prepared image expected an object root".into());
    };
    if root.contains_key("shared_payloads") {
        return Err("prepared image input already contains shared_payloads".into());
    }
    let mut encoder = Encoder::default();
    let root = encoder.visit(document)?;
    Ok(Image {
        fields: encoder.fields,
        nodes: encoder.nodes,
        root,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn indexed_rows_preserve_source_identity_and_topological_order() {
        let a = json!({"type_id":17,"name":"same"});
        let b = json!({"type_id":18,"name":"same"});
        let image = wire(encode(&json!({"values":[a,a,b]})).unwrap());
        assert_eq!(image["schema"], "lean-miri-prepared-image");
        let rows = image["nodes"].as_array().unwrap();
        for (index, row) in rows.iter().enumerate() {
            if row[0] == 5 {
                for id in row[1].as_array().unwrap() {
                    assert!(id.as_u64().unwrap() < (index as u64));
                }
            }
            if row[0] == 6 {
                for pair in row[1].as_array().unwrap() {
                    assert!(pair[1].as_u64().unwrap() < (index as u64));
                }
            }
        }
        assert!(rows.iter().any(|row| row[0] == 3 && row[1] == 17));
        assert!(rows.iter().any(|row| row[0] == 3 && row[1] == 18));
    }
}

#[cfg(test)]
mod roundtrip_tests {
    use super::*;

    fn reconstruct(image: &Value) -> Value {
        let fields = image["fields"].as_array().unwrap();
        let mut values: Vec<Value> = Vec::new();
        for row in image["nodes"].as_array().unwrap() {
            let value = match row[0].as_u64().unwrap() {
                0 => Value::Null,
                1 => json!(false),
                2 => json!(true),
                3 | 4 => row[1].clone(),
                5 => Value::array(
                    row[1]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|id| values[id.as_u64().unwrap() as usize].clone())
                        .collect(),
                ),
                6 => Value::object(
                    row[1]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|pair| {
                            let name = fields[pair[0].as_u64().unwrap() as usize]
                                .as_str()
                                .unwrap()
                                .to_owned();
                            (name, values[pair[1].as_u64().unwrap() as usize].clone())
                        })
                        .collect(),
                ),
                tag => panic!("unexpected row tag {tag}"),
            };
            values.push(value);
        }
        values[image["root"].as_u64().unwrap() as usize].clone()
    }

    #[test]
    fn exact_wire_roundtrip_including_numeric_spelling_and_field_order() {
        let mut source = json!({"type_id": 17, "allocation_id": 18,
            "a.b%[": [null, false, true, -0.0, 0.0, 1.0, 1, -17,
                "日本語\nquoted\"", [], {}], "z": {"instance_id": 19}});
        for index in 0..32 {
            source["nested"] = json!([source["z"], {"index": index}]);
            let image = wire(encode(&source).unwrap());
            assert_eq!(reconstruct(&image).to_string(), source.to_string());
        }
    }

    #[test]
    fn exponentially_repeated_source_is_visited_as_a_graph() {
        let mut value = json!({"type_id": 17});
        for _ in 0..64 {
            value = json!({"left": value, "right": value});
        }
        let image = wire(encode(&value).unwrap());
        assert!(image["nodes"].as_array().unwrap().len() < 140);
        let reconstructed = reconstruct(&image);
        let object = reconstructed.as_object().unwrap();
        assert_eq!(object["left"].identity(), object["right"].identity());
    }

    #[test]
    fn reserved_transport_fields_are_rejected() {
        assert!(encode(&json!({"nested": {"$lean_miri_shared_ref": 0}})).is_err());
        assert!(encode(&json!({"shared_payloads": null})).is_err());
    }
}
