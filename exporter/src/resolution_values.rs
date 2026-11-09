//! Concrete call-resolution evidence retained by semantic MIR bodies.
use serde::Serialize;
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Callee {
    ResolvedInstance {
        function_type: u64,
        instance_id: u64,
        dispatch_slot: Option<usize>,
        fn_abi: u64,
        virtual_resolution: Option<VirtualResolution>,
    },
    VirtualDispatch {
        function_type: u64,
        instance_id: u64,
        dispatch_slot: Option<usize>,
        fn_abi: u64,
        virtual_resolution: Option<VirtualResolution>,
    },
    IndirectFunctionPointer {
        function_type: u64,
        signature: super::pool_type::FunctionSignature,
        extra_argument_types: Vec<u64>,
        fn_abi: u64,
    },
}
#[derive(Serialize)]
pub(super) struct VirtualResolution {
    pub instance_id: u64,
    pub method_definition: u64,
    pub dispatch_slot: usize,
    pub candidate_query_ids: Vec<u64>,
    pub selection: &'static str,
}
