//! Semantic compiler instance identities and their executable or dispatch payloads.
use super::pool_values::GenericArgument;
use serde::Serialize;
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum InstanceKind {
    Item {
        def_id: u64,
    },
    Intrinsic {
        def_id: u64,
    },
    LlvmIntrinsic {
        def_id: u64,
    },
    Virtual {
        def_id: u64,
        dispatch_slot: usize,
    },
    Shim {
        #[serde(flatten)]
        shim: ShimKind,
    },
}
#[derive(Serialize)]
#[serde(tag = "shim_kind", rename_all = "snake_case")]
pub(super) enum ShimKind {
    Vtable {
        def_id: u64,
    },
    Reify {
        def_id: u64,
        reason: Option<&'static str>,
    },
    FnPointer {
        def_id: u64,
        function_type: u64,
    },
    ClosureOnce {
        call_once_def_id: u64,
        closure_def_id: u64,
        track_caller: bool,
    },
    ConstructCoroutineInClosure {
        coroutine_closure_def_id: u64,
        receiver_by_ref: bool,
    },
    ThreadLocal {
        def_id: u64,
    },
    FutureDropPoll {
        def_id: u64,
        proxy_coroutine_type: u64,
        implementation_coroutine_type: u64,
    },
    DropGlue {
        def_id: u64,
        drop_type: Option<u64>,
    },
    Clone {
        def_id: u64,
        clone_type: u64,
    },
    FnPointerAsPointer {
        def_id: u64,
        function_type: u64,
    },
    FnPointerFromPointer {
        def_id: u64,
        function_type: u64,
    },
    AsyncDropGlueConstructor {
        def_id: u64,
        drop_type: u64,
    },
    AsyncDropGlue {
        def_id: u64,
        coroutine_type: u64,
    },
}
#[derive(Serialize)]
pub(super) struct Instance {
    pub instance_id: u64,
    pub instance_kind: InstanceKind,
    pub def_id: u64,
    pub def_path: String,
    pub generic_args: Vec<GenericArgument>,
    #[serde(flatten)]
    pub data: InstanceData,
}
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum InstanceData {
    IntrinsicDispatch {
        fallback_instance: Option<u64>,
        reason: &'static str,
    },
    ForeignItemNoMir {
        foreign_item: bool,
        symbol_name: String,
        reason: &'static str,
    },
    VirtualDispatchTarget {
        dispatch_slot: usize,
        body_status: &'static str,
        virtual_identity: VirtualIdentity,
        reason: &'static str,
    },
    InstanceMir {
        body: u64,
        promoted_bodies: Vec<PromotedBody>,
    },
    IdentityOnly {
        reason: &'static str,
    },
}
#[derive(Serialize)]
pub(super) struct VirtualIdentity {
    pub function_type: u64,
    pub fn_abi: u64,
}
#[derive(Serialize)]
pub(super) struct PromotedBody {
    pub promoted_index: u32,
    pub body: u64,
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn shim_serialization_retains_both_discriminators_and_null_drop_type() {
        let kind = InstanceKind::Shim {
            shim: ShimKind::DropGlue {
                def_id: 12,
                drop_type: None,
            },
        };
        assert_eq!(
            serde_json::to_value(kind).unwrap(),
            json!({"kind":"shim","shim_kind":"drop_glue","def_id":12,"drop_type":null})
        );
    }

    #[test]
    fn identity_row_has_no_executable_mir_fields() {
        let row = Instance {
            instance_id: 0,
            instance_kind: InstanceKind::Item { def_id: 1 },
            def_id: 1,
            def_path: "example".into(),
            generic_args: vec![],
            data: InstanceData::IdentityOnly {
                reason: "compiler instance identity; source MIR was not demanded",
            },
        };
        assert_eq!(
            serde_json::to_value(row).unwrap(),
            json!({"instance_id":0,"instance_kind":{"kind":"item","def_id":1},"def_id":1,"def_path":"example","generic_args":[],"kind":"identity_only","reason":"compiler instance identity; source MIR was not demanded"})
        );
    }
}
