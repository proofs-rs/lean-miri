//! Concrete call-resolution evidence retained by semantic MIR bodies.
use serde::Serialize;
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Callee<C = PendingCandidates> {
    LlvmIntrinsic { function_type: u64, instance_id: u64 },
    SourceInstance { function_type: u64, instance_id: u64 },
    ResolvedInstance {
        function_type: u64,
        instance_id: u64,
        dispatch_slot: Option<usize>,
        fn_abi: u64,
        virtual_resolution: Option<VirtualResolution<C>>,
    },
    VirtualDispatch {
        function_type: u64,
        instance_id: u64,
        dispatch_slot: Option<usize>,
        fn_abi: u64,
        virtual_resolution: Option<VirtualResolution<C>>,
    },
    IndirectFunctionPointer {
        function_type: u64,
        signature: super::pool_type::FunctionSignature,
        extra_argument_types: Vec<u64>,
        fn_abi: u64,
    },
}
#[derive(Serialize)]
pub(super) struct VirtualResolution<C = PendingCandidates> {
    pub instance_id: u64,
    pub method_definition: u64,
    pub dispatch_slot: usize,
    pub candidate_query_ids: C,
    pub selection: &'static str,
}

pub(super) struct PendingCandidates;
impl VirtualResolution<PendingCandidates> {
    fn finish(
        self,
        candidates: &std::collections::HashMap<u64, Vec<u64>>,
    ) -> VirtualResolution<Vec<u64>> {
        VirtualResolution {
            instance_id: self.instance_id,
            method_definition: self.method_definition,
            dispatch_slot: self.dispatch_slot,
            candidate_query_ids: candidates
                .get(&self.instance_id)
                .cloned()
                .unwrap_or_default(),
            selection: self.selection,
        }
    }
}
impl Callee<PendingCandidates> {
    pub fn finish(self, candidates: &std::collections::HashMap<u64, Vec<u64>>) -> Callee<Vec<u64>> {
        match self {
            Self::LlvmIntrinsic { function_type, instance_id } => Callee::LlvmIntrinsic { function_type, instance_id },
            Self::SourceInstance { function_type, instance_id } => Callee::SourceInstance { function_type, instance_id },
            Self::ResolvedInstance {
                function_type,
                instance_id,
                dispatch_slot,
                fn_abi,
                virtual_resolution,
            } => Callee::ResolvedInstance {
                function_type,
                instance_id,
                dispatch_slot,
                fn_abi,
                virtual_resolution: virtual_resolution.map(|item| item.finish(candidates)),
            },
            Self::VirtualDispatch {
                function_type,
                instance_id,
                dispatch_slot,
                fn_abi,
                virtual_resolution,
            } => Callee::VirtualDispatch {
                function_type,
                instance_id,
                dispatch_slot,
                fn_abi,
                virtual_resolution: virtual_resolution.map(|item| item.finish(candidates)),
            },
            Self::IndirectFunctionPointer {
                function_type,
                signature,
                extra_argument_types,
                fn_abi,
            } => Callee::IndirectFunctionPointer {
                function_type,
                signature,
                extra_argument_types,
                fn_abi,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn candidate_lookup_uses_the_exact_virtual_instance() {
        let candidates = std::collections::HashMap::from([(8, vec![2, 4]), (9, vec![6])]);
        let resolution = VirtualResolution {
            instance_id: 8,
            method_definition: 1,
            dispatch_slot: 3,
            candidate_query_ids: PendingCandidates,
            selection: "runtime",
        }
        .finish(&candidates);
        assert_eq!(resolution.candidate_query_ids, vec![2, 4]);
        let absent = VirtualResolution {
            instance_id: 10,
            method_definition: 1,
            dispatch_slot: 3,
            candidate_query_ids: PendingCandidates,
            selection: "runtime",
        }
        .finish(&candidates);
        assert!(absent.candidate_query_ids.is_empty());
    }
}
