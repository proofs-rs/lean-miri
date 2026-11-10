//! Typed compiler-evaluated MIR constants, preserving pointer provenance.
use serde::Serialize;
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(crate) enum Value {
    ZeroSized {
        #[serde(rename = "type")]
        ty: u64,
    },
    Scalar {
        #[serde(rename = "type")]
        ty: u64,
        bits_unsigned: String,
    },
    SliceAllocation {
        #[serde(rename = "type")]
        ty: u64,
        allocation: u64,
        metadata_length: u64,
    },
    IndirectAllocation {
        #[serde(rename = "type")]
        ty: u64,
        allocation: u64,
        offset_bytes: u64,
    },
    PointerScalar {
        #[serde(rename = "type")]
        ty: u64,
        allocation: u64,
        offset_bytes: u64,
        immutable: bool,
        shared_ref: bool,
    },
    PointerScalarWithoutProvenance {
        #[serde(rename = "type")]
        ty: u64,
        address: String,
        address_width_bytes: u64,
    },
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(crate) enum Annotation {
    AnnotationRef { index: u32 },
}
#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(crate) enum Constant {
    EvaluatedConst { value: Value },
}
#[derive(Clone, Debug, Serialize)]
pub(crate) struct Operand {
    #[serde(rename = "type")]
    pub ty: u64,
    pub user_type_annotation: Option<Annotation>,
    pub constant: Constant,
    pub span: u64,
}
#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn pointer_scalar_serialization_preserves_provenance_and_flags() {
        let value = Value::PointerScalar {
            ty: 7,
            allocation: 11,
            offset_bytes: 13,
            immutable: true,
            shared_ref: false,
        };
        assert_eq!(
            serde_json::to_value(value).unwrap(),
            json!({"kind":"pointer_scalar","type":7,"allocation":11,"offset_bytes":13,"immutable":true,"shared_ref":false})
        );
    }

    #[test]
    fn integer_pointer_serialization_keeps_address_as_decimal_string() {
        let value = Value::PointerScalarWithoutProvenance {
            ty: 3,
            address: u64::MAX.to_string(),
            address_width_bytes: 8,
        };
        assert_eq!(
            serde_json::to_value(value).unwrap(),
            json!({"kind":"pointer_scalar_without_provenance","type":3,"address":"18446744073709551615","address_width_bytes":8})
        );
    }
}
