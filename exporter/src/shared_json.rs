//! Exact payload sharing at the closed-document boundary. Compiler-keyed tables
//! keep their identities; only the storage for their complete values is shared.
use serde::{Serialize, Serializer};
use std::collections::HashMap;

#[derive(Clone, Debug, Serialize)]
#[serde(untagged)]
pub(super) enum Shared<T> {
    Value(T),
    Reference(u64),
}
impl<T> From<T> for Shared<T> {
    fn from(value: T) -> Self {
        Self::Value(value)
    }
}
impl<T> Shared<T> {
    pub(super) fn try_map<U>(
        self,
        f: impl FnOnce(T) -> Result<U, String>,
    ) -> Result<Shared<U>, String> {
        match self {
            Self::Value(value) => Ok(Shared::Value(f(value)?)),
            Self::Reference(_) => Err("payload pooled before semantic resolution".into()),
        }
    }
}

pub(super) struct Payloads<T> {
    // Complete serialization is the equality key, not a digest. No collision can
    // merge unequal payloads, including reference IDs, nulls and explicit false.
    ids: HashMap<Vec<u8>, u64>,
    values: Vec<T>,
}
impl<T> Default for Payloads<T> {
    fn default() -> Self {
        Self {
            ids: HashMap::new(),
            values: Vec::new(),
        }
    }
}
impl<T: Serialize> Serialize for Payloads<T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.values.serialize(serializer)
    }
}
impl<T: Serialize> Payloads<T> {
    fn share(&mut self, slot: &mut Shared<T>) -> Result<(), String> {
        let Shared::Value(value) = slot else {
            return Err("payload pooled twice".into());
        };
        let key = serde_json::to_vec(value)
            .map_err(|error| format!("cannot key shared payload: {error}"))?;
        if let Some(&id) = self.ids.get(&key) {
            *slot = Shared::Reference(id);
        } else {
            let id = self.values.len() as u64;
            let Shared::Value(value) = std::mem::replace(slot, Shared::Reference(id)) else {
                unreachable!()
            };
            self.ids.insert(key, id);
            self.values.push(value);
        }
        Ok(())
    }
}

#[derive(Default, Serialize)]
pub(super) struct Values {
    layout_values: Payloads<crate::pool_layout::Layout>,
    abi_arguments: Payloads<crate::pool_layout::ArgAbi>,
    boolean_queries: Payloads<crate::pool_type::BooleanQueries>,
    discriminants: Payloads<crate::pool_type::Discriminants>,
    initialization_ranges: Payloads<Vec<crate::allocation_values::InitializationRange>>,
    relocations: Payloads<Vec<crate::allocation_values::Relocation>>,
    backtrace_spans: Payloads<Vec<crate::pool_body::BacktraceSpan>>,
    statement_kinds: Payloads<crate::pool_body::StatementKind<u64>>,
    source_infos: Payloads<crate::pool_body::SourceInfo>,
}
impl Values {
    fn memory(&mut self, memory: &mut crate::allocation_values::Memory) -> Result<(), String> {
        self.initialization_ranges
            .share(&mut memory.initialization_ranges)?;
        self.relocations.share(&mut memory.relocations)
    }
}

/// Called once, after all semantic references have been resolved. In particular,
/// relocation targets and statement query IDs participate in exact equality.
pub(super) fn freeze(document: &mut crate::ExportDocument) -> Result<(), String> {
    let pools = &mut document.shared_values;
    for layout in &mut document.layouts {
        pools.layout_values.share(layout)?;
    }
    for abi in &mut document.fn_abis {
        pools.abi_arguments.share(&mut abi.ret)?;
        for argument in &mut abi.arguments {
            pools.abi_arguments.share(argument)?;
        }
    }
    for ty in &mut document.types {
        pools
            .boolean_queries
            .share(&mut ty.compiler_facts.boolean_queries)?;
        pools
            .discriminants
            .share(&mut ty.compiler_facts.discriminants)?;
    }
    for entry in &mut document.allocations {
        if let crate::allocation_values::Entry::Single(allocation) = entry {
            use crate::allocation_values::AllocationData;
            match &mut allocation.data {
                AllocationData::Memory { memory } => pools.memory(memory)?,
                AllocationData::Static {
                    initializer: Some(memory),
                    ..
                } => pools.memory(memory)?,
                _ => (),
            }
        }
    }
    for row in &mut document.compiler_coroutine_coverage.coroutines {
        for field in &mut row.layout.field_tys {
            pools.source_infos.share(&mut field.source_info)?;
        }
    }
    for body in document.bodies.iter_mut().filter_map(|seed|match seed {
        crate::pool_body::BodySeed::Material{body}=>Some(body),
        crate::pool_body::BodySeed::CopyTemplate{..}|crate::pool_body::BodySeed::NoopDrop{..}|crate::pool_body::BodySeed::FnPointerShim{..}=>None,
    }).chain(document.compiler_coroutine_coverage.auxiliary_bodies.iter_mut().map(|row| &mut row.body)) {
        pools.backtrace_spans.share(&mut body.backtrace_spans)?;
        for local in &mut body.locals {
            pools.source_infos.share(&mut local.source_info)?;
        }
        for block in &mut body.basic_blocks {
            for statement in &mut block.statements {
                pools.source_infos.share(&mut statement.source_info)?;
                if let Shared::Value(crate::pool_body::StatementKind::Assign {
                    rvalue: crate::pool_body::Rvalue::ThreadLocalRef { initializer, .. },
                    ..
                }) = &mut statement.kind
                {
                    pools.memory(&mut initializer.allocation)?;
                }
                pools.statement_kinds.share(&mut statement.kind)?;
            }
            if let Some(terminator) = &mut block.terminator {
                pools.source_infos.share(&mut terminator.source_info)?;
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn complete_values_share_without_dropping_explicit_defaults() {
        #[derive(Serialize)]
        struct Value {
            present: bool,
            absent: Option<u64>,
            references: Vec<u64>,
        }
        let mut pool = Payloads::default();
        let mut first = Shared::from(Value {
            present: false,
            absent: None,
            references: vec![],
        });
        let mut same = Shared::from(Value {
            present: false,
            absent: None,
            references: vec![],
        });
        let mut different = Shared::from(Value {
            present: false,
            absent: None,
            references: vec![1],
        });
        pool.share(&mut first).unwrap();
        pool.share(&mut same).unwrap();
        pool.share(&mut different).unwrap();
        assert_eq!(serde_json::to_string(&first).unwrap(), "0");
        assert_eq!(serde_json::to_string(&same).unwrap(), "0");
        assert_eq!(serde_json::to_string(&different).unwrap(), "1");
        assert_eq!(
            serde_json::to_string(&pool).unwrap(),
            r#"[{"present":false,"absent":null,"references":[]},{"present":false,"absent":null,"references":[1]}]"#
        );
    }
    #[test]
    fn empty_array_is_a_real_shared_value() {
        let mut pool = Payloads::<Vec<u64>>::default();
        let mut a = Shared::from(vec![]);
        let mut b = Shared::from(vec![]);
        pool.share(&mut a).unwrap();
        pool.share(&mut b).unwrap();
        assert_eq!(serde_json::to_string(&pool).unwrap(), "[[]]");
        assert!(pool.share(&mut a).is_err());
    }
}

#[cfg(test)]
mod semantic_tests {
    use super::*;
    use crate::allocation_values::Relocation;

    #[test]
    fn relocation_targets_and_permissions_are_part_of_equality() {
        let relocation = |target, immutable, shared_ref| {
            vec![Relocation {
                storage_offset_bytes: 0,
                target,
                target_offset_encoded_bytes: "0000000000000000".into(),
                immutable,
                shared_ref,
            }]
        };
        let mut pool = Payloads::default();
        let mut first = Shared::from(relocation(1, false, false));
        let mut same = Shared::from(relocation(1, false, false));
        let mut target = Shared::from(relocation(2, false, false));
        let mut immutable = Shared::from(relocation(1, true, false));
        let mut shared_ref = Shared::from(relocation(1, false, true));
        for value in [
            &mut first,
            &mut same,
            &mut target,
            &mut immutable,
            &mut shared_ref,
        ] {
            pool.share(value).unwrap();
        }
        assert_eq!(pool.values.len(), 4);
        assert_eq!(
            serde_json::to_string(&first).unwrap(),
            serde_json::to_string(&same).unwrap()
        );
    }

    #[test]
    fn source_scope_context_is_part_of_source_info_equality() {
        let mut pool = Payloads::default();
        let mut first = Shared::from(crate::pool_body::SourceInfo { span: 7, scope: 1 });
        let mut other_scope = Shared::from(crate::pool_body::SourceInfo { span: 7, scope: 2 });
        let mut other_span = Shared::from(crate::pool_body::SourceInfo { span: 8, scope: 1 });
        for value in [&mut first, &mut other_scope, &mut other_span] {
            pool.share(value).unwrap();
        }
        assert_eq!(pool.values.len(), 3);
    }

    #[test]
    fn complete_layout_equality_preserves_every_original_layout_slot() {
        use crate::pool_layout::{BackendRepr, FieldOffsets, Fields, FullLayout, Layout, Variants};
        let layout = |seed| {
            Shared::from(Layout::Material(FullLayout {
                size_bytes: 0,
                abi_align_bytes: 1,
                unadjusted_abi_align_bytes: 1,
                max_repr_align_bytes: None,
                repr_c: false,
                uninhabited: false,
                fields: Fields::Primitive { field_count: 0 },
                field_offsets_bytes: FieldOffsets::Explicit(vec![]),
                variants: Variants::Single { variant_index: 0 },
                backend_repr: BackendRepr::Memory { sized: true },
                largest_niche: None,
                randomization_seed: seed,
            }))
        };
        let mut slots = vec![layout(7), layout(7), layout(8)];
        let mut pool = Payloads::default();
        for slot in &mut slots {
            pool.share(slot).unwrap();
        }
        assert_eq!(serde_json::to_string(&slots).unwrap(), "[0,0,1]");
        assert_eq!(pool.values.len(), 2);
        let payload = serde_json::to_value(&pool).unwrap();
        assert_eq!(payload[0]["max_repr_align_bytes"], serde_json::Value::Null);
        assert_eq!(payload[0]["repr_c"], false);
        assert_eq!(payload[0]["field_offsets_bytes"], serde_json::json!([]));
    }

    #[test]
    fn compact_array_formula_equality_includes_stride_and_count() {
        use crate::pool_layout::FieldOffsets;
        let formula = |stride, count| {
            Shared::from(FieldOffsets::ArrayFormula {
                kind: "array",
                stride_bytes: stride,
                field_count: count,
            })
        };
        let mut slots = vec![
            formula(4, 1_000_000),
            formula(4, 1_000_000),
            formula(8, 1_000_000),
            formula(4, 999_999),
        ];
        let mut pool = Payloads::default();
        for slot in &mut slots {
            pool.share(slot).unwrap();
        }
        assert_eq!(serde_json::to_string(&slots).unwrap(), "[0,0,1,2]");
        let payload = serde_json::to_string(&pool).unwrap();
        assert!(payload.len() < 250);
        assert_eq!(pool.values.len(), 3);
    }

    #[test]
    fn abi_argument_sharing_requires_complete_type_layout_and_mode_equality() {
        use crate::pool_layout::{ArgAbi, PassMode};
        let argument = |ty, layout, mode| Shared::from(ArgAbi { ty, layout, mode });
        let attributes = |size| {
            let mut value = rustc_target::callconv::ArgAttributes::new();
            value.pointee_size = rustc_abi::Size::from_bytes(size);
            crate::pool_layout::ArgAttributes::new(value)
        };
        let mut arguments = vec![
            argument(3, 5, PassMode::Ignore),
            argument(3, 5, PassMode::Ignore),
            argument(4, 5, PassMode::Ignore),
            argument(3, 6, PassMode::Ignore),
            argument(3, 5, PassMode::Pair {
                first: attributes(0),
                second: attributes(0),
            }),
            argument(3, 5, PassMode::Pair { first: attributes(0), second: attributes(8) }),
        ];
        let mut pool = Payloads::default();
        for argument in &mut arguments {
            pool.share(argument).unwrap();
        }
        assert_eq!(serde_json::to_string(&arguments).unwrap(), "[0,0,1,2,3,4]");
        assert_eq!(pool.values.len(), 5);
    }

    #[test]
    fn empty_document_still_emits_every_payload_pool() {
        let serialized = serde_json::to_value(Values::default()).unwrap();
        for field in [
            "layout_values",
            "abi_arguments",
            "boolean_queries",
            "discriminants",
            "initialization_ranges",
            "relocations",
            "backtrace_spans",
            "statement_kinds",
            "source_infos",
        ] {
            assert_eq!(serialized[field], serde_json::json!([]));
        }
    }
}
