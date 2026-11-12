//! Semantic MIR body metadata. References are exporter-local pool indices.
use serde::Serialize;
use crate::shared_json::Shared;

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Phase {
    Built,
    Analysis { phase: AnalysisPhase },
    Runtime { phase: RuntimePhase },
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum AnalysisPhase {
    Initial,
    PostCleanup,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum RuntimePhase {
    Initial,
    PostCleanup,
    Optimized,
}

#[derive(Clone, Debug, Serialize)]
pub(super) struct SourceInfo {
    pub span: u64,
    pub scope: u32,
}


#[derive(Clone, Debug, Serialize)]
pub(super) struct SourcePosition {
    pub byte_position: u32,
    pub line: usize,
    pub zero_based_char_column: usize,
    pub filename: u64,
}

#[derive(Clone, Debug, Serialize)]
pub(super) struct BacktraceSpan {
    pub span: u64,
    pub source_position: SourcePosition,
}

#[derive(Clone, Debug, Serialize)]
pub(super) struct InlinedScope {
    pub instance_id: u64,
    pub callsite_span: u64,
    pub requires_caller_location: bool,
}

#[derive(Clone, Debug, Serialize)]
pub(super) struct SourceScope {
    pub scope: u32,
    pub parent: Option<u32>,
    pub span: u64,
    pub inlined: Option<InlinedScope>,
    pub inlined_parent_scope: Option<u32>,
}

#[derive(Clone, Debug, Serialize)]
pub(super) struct Local {
    pub local: u32,
    pub r#type: u64,
    pub source_info: Shared<SourceInfo>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind")]
pub(super) enum ProjectionKind {
    Deref,
    Field {
        index: u32,
        field_type: u64,
    },
    Index {
        local: u32,
    },
    ConstantIndex {
        offset: u64,
        min_length: u64,
        from_end: bool,
    },
    Subslice {
        from: u64,
        to: u64,
        from_end: bool,
    },
    Downcast {
        name: Option<String>,
        variant_index: u32,
    },
    OpaqueCast {
        cast_type: u64,
    },
    UnwrapUnsafeBinder {
        inner_type: u64,
    },
    PhantomDeref,
}

#[derive(Clone, Debug, Serialize)]
pub(super) struct Projection {
    #[serde(flatten)]
    pub kind: ProjectionKind,
    pub resulting_type: u64,
}

#[derive(Clone, Debug, Serialize)]
pub(super) struct Place {
    pub local: u32,
    pub projection: Vec<Projection>,
    pub r#type: u64,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum RuntimeCheck {
    UbChecks { enabled: bool },
    ContractChecks { enabled: bool },
    OverflowChecks { enabled: bool },
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum FakeReadCause {
    MatchGuard,
    MatchedPlace { hoisted_from: Option<u64> },
    GuardBinding,
    LetBinding { hoisted_from: Option<u64> },
    Index,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Variance {
    Covariant,
    Contravariant,
    Invariant,
    Bivariant,
}

#[derive(Clone, Debug, Serialize)]
pub(super) struct HirId {
    pub owner_def_id: u64,
    pub local_id: u32,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Coverage {
    Point {
        point_kind: CoveragePoint,
        hir_id: HirId,
    },
    BlockMarker {
        id: u32,
    },
    VirtualCounter {
        bcb: u32,
    },
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum CoveragePoint {
    Expr,
    ImplicitElse,
    FunctionEnd,
}

#[derive(Clone, Debug, Serialize)]
pub(super) struct UserTypeProjection {
    pub base_index: u32,
    pub projections: Vec<UserProjection>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind")]
pub(super) enum UserProjection {
    Deref,
    Field {
        index: u32,
    },
    Index,
    ConstantIndex {
        offset: u64,
        min_length: u64,
        from_end: bool,
    },
    Subslice {
        from: u64,
        to: u64,
        from_end: bool,
    },
    Downcast {
        name: Option<String>,
        variant_index: u32,
    },
    OpaqueCast,
    UnwrapUnsafeBinder,
    PhantomDeref,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind")]
pub(super) enum Unwind {
    Continue,
    Unreachable,
    Terminate { reason: UnwindTerminateReason },
    Cleanup { target: u32 },
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum UnwindTerminateReason {
    Abi,
    InCleanup,
}

#[derive(Serialize)]
#[serde(tag = "kind")]
pub(super) enum Operand {
    Copy {
        place: Place,
    },
    Move {
        place: Place,
    },
    Constant {
        constant: crate::pool_constant::Operand,
    },
    RuntimeChecks {
        check: RuntimeCheck,
    },
}

#[derive(Serialize)]
#[serde(tag = "variant")]
pub(super) enum StatementKind<Q = VtableQueryKey> {
    Assign {
        place: Place,
        rvalue: Rvalue<Q>,
    },
    FakeRead {
        cause: FakeReadCause,
        place: Place,
    },
    SetDiscriminant {
        place: Place,
        variant_index: u32,
    },
    StorageLive {
        local: u32,
    },
    StorageDead {
        local: u32,
    },
    PlaceMention {
        place: Place,
    },
    AscribeUserType {
        execution: &'static str,
        place: Place,
        user_type_projection: UserTypeProjection,
        variance: Variance,
    },
    Coverage {
        execution: &'static str,
        coverage: Coverage,
    },
    Intrinsic {
        #[serde(flatten)]
        intrinsic: Intrinsic,
    },
    ConstEvalCounter,
    Nop,
    BackwardIncompatibleDropHint {
        place: Place,
        reason: DropHintReason,
    },
}

#[derive(Serialize)]
#[serde(tag = "intrinsic")]
pub(super) enum Intrinsic {
    Assume {
        value: Operand,
    },
    CopyNonOverlapping {
        src: Operand,
        dst: Operand,
        count: Operand,
    },
}

#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum DropHintReason {
    #[serde(rename = "edition_2024")]
    Edition2024,
}

#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum BorrowKind {
    Shared,
    Fake {
        fake_kind: &'static str,
        retag_mode: &'static str,
    },
    Mutable {
        mutability_kind: &'static str,
    },
}

#[derive(Serialize)]
pub(super) struct Retag {
    pub kind: &'static str,
    pub performs_retag: bool,
}
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum RawPointerKind {
    Mutable,
    Constant,
    MetadataOnly,
}
#[derive(Serialize)]
pub(super) struct Operator {
    pub kind: &'static str,
}
#[derive(Serialize)]
pub(super) struct ThreadLocalInitializer {
    pub allocation: crate::allocation_values::Memory,
}

#[derive(Serialize)]
#[serde(tag = "kind")]
pub(super) enum CastKind {
    PointerExposeProvenance,
    PointerWithExposedProvenance,
    PointerCoercion {
        coercion: PointerCoercion,
        source: CoercionSource,
    },
    IntToInt,
    FloatToInt,
    FloatToFloat,
    IntToFloat,
    PtrToPtr,
    FnPtrToPtr,
    Transmute,
    BoxDerefTransmute,
    Subtype,
}
#[derive(Serialize)]
#[serde(tag = "kind")]
pub(super) enum PointerCoercion {
    ReifyFnPointer { safety: crate::pool_type::Safety },
    UnsafeFnPointer,
    ClosureFnPointer { safety: crate::pool_type::Safety },
    MutToConstPointer,
    ArrayToPointer,
    Unsize,
}
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum CoercionSource {
    AsCast,
    Implicit,
}

#[derive(Serialize)]
#[serde(tag = "kind")]
pub(super) enum AggregateKind {
    Array {
        element_type: u64,
    },
    Tuple,
    Adt {
        def_id: u64,
        def_path: String,
        variant_index: u32,
        generic_args: Vec<crate::pool_values::GenericArgument>,
        user_type_annotation: Option<crate::pool_constant::Annotation>,
        active_union_field: Option<u32>,
    },
    Closure {
        def_id: u64,
        def_path: String,
        generic_args: Vec<crate::pool_values::GenericArgument>,
    },
    Coroutine {
        def_id: u64,
        def_path: String,
        generic_args: Vec<crate::pool_values::GenericArgument>,
    },
    CoroutineClosure {
        def_id: u64,
        def_path: String,
        generic_args: Vec<crate::pool_values::GenericArgument>,
    },
    RawPtr {
        pointee_type: u64,
        mutability: crate::pool_type::Mutability,
    },
}

#[derive(Serialize)]
#[serde(tag = "kind")]
pub(super) enum Rvalue<Q = VtableQueryKey> {
    Use {
        operand: Operand,
        retag: Retag,
    },
    Repeat {
        operand: Operand,
        count: u64,
    },
    Ref {
        region: crate::pool_values::Region,
        borrow_kind: BorrowKind,
        place: Place,
    },
    ThreadLocalRef {
        global_info: crate::allocation_values::StaticGlobalInfo,
        def_id: u64,
        def_path: String,
        initializer: ThreadLocalInitializer,
    },
    RawPtr {
        pointer_kind: RawPointerKind,
        place: Place,
    },
    Cast {
        cast_kind: CastKind,
        operand: Operand,
        target_type: u64,
        vtable_allocation: Option<VtableAllocation>,
        vtable_query: Option<VtableQuery<Q>>,
        vtable_probe: Option<VtableProbe>,
    },
    BinaryOp {
        operator: Operator,
        left: Operand,
        right: Operand,
        implicit_overflow_tuple_type: Option<u64>,
    },
    UnaryOp {
        operator: Operator,
        operand: Operand,
    },
    Discriminant {
        place: Place,
    },
    Aggregate {
        aggregate_kind: AggregateKind,
        operands: Vec<Operand>,
    },
    CopyForDeref {
        place: Place,
    },
    WrapUnsafeBinder {
        operand: Operand,
        r#type: u64,
    },
    Reborrow {
        r#type: u64,
        mutability: crate::pool_type::Mutability,
        place: Place,
    },
}

#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum VtableAllocation {
    SameDynamicVtableNoop {
        r#type: u64,
    },
    DynamicVtableUpcast {
        source_type: u64,
        target_type: u64,
        source_pointee_type: u64,
        target_pointee_type: u64,
        source_tail_type: u64,
        target_tail_type: u64,
        supertrait_slot_query: SupertraitSlotQuery,
        runtime_vtable: &'static str,
    },
}
#[derive(Serialize)]
pub(super) struct SupertraitSlotQuery {
    pub query_kind: &'static str,
    pub typing_env: &'static str,
    pub input_source: u64,
    pub input_target: u64,
}
#[derive(Serialize)]
pub(super) struct VtableQuery<Q = VtableQueryKey> {
    pub source_type: u64,
    pub target_type: u64,
    pub source_pointee_type: u64,
    pub target_pointee_type: u64,
    pub input_type: u64,
    pub input_predicates: Vec<u64>,
    pub source_tail_type: u64,
    pub target_tail_type: u64,
    pub query_id: Q,
}
pub(super) struct VtableQueryKey {
    pub input_type_id: u64,
    pub input_predicate_ids: Vec<u64>,
}
// The exporter currently emits no cast vtable probes. This uninhabited type
// prevents an arbitrary payload from entering that optional schema position.
#[derive(Serialize)]
pub(super) enum VtableProbe {}

pub(super) enum UnsizeVtable {
    Allocation(VtableAllocation),
    Query(VtableQuery),
}

#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum CoroutineKind {
    Desugared {
        desugaring: &'static str,
        source: &'static str,
    },
    Coroutine {
        movability: &'static str,
    },
}

#[derive(Serialize)]
#[serde(tag = "kind")]
pub(super) enum AssertMessage {
    BoundsCheck {
        length: Operand,
        index: Operand,
    },
    Overflow {
        operator: Operator,
        left: Operand,
        right: Operand,
    },
    OverflowNeg {
        operand: Operand,
    },
    DivisionByZero {
        operand: Operand,
    },
    RemainderByZero {
        operand: Operand,
    },
    ResumedAfterReturn {
        coroutine_kind: CoroutineKind,
    },
    ResumedAfterPanic {
        coroutine_kind: CoroutineKind,
    },
    ResumedAfterDrop {
        coroutine_kind: CoroutineKind,
    },
    MisalignedPointerDereference {
        required: Operand,
        found: Operand,
    },
    NullPointerDereference,
    NullReferenceConstructed,
    InvalidEnumConstruction {
        operand: Operand,
    },
}

#[derive(Serialize)]
#[serde(tag = "kind")]
pub(super) enum LoopHint {
    Hint,
    Full,
    Never,
    Count { count: u32 },
}
#[derive(Serialize)]
pub(super) struct SwitchTarget {
    pub value: String,
    pub target: u32,
}
#[derive(Serialize)]
pub(super) struct CallArgument {
    pub operand: Operand,
    pub span: u64,
}
#[derive(Serialize)]
pub(super) struct CallSource {
    pub kind: &'static str,
}

#[derive(Serialize)]
#[serde(tag = "variant")]
pub(super) enum TerminatorKind<C = crate::resolution_values::PendingCandidates> {
    Goto {
        target: u32,
        loop_hints: Vec<LoopHint>,
    },
    SwitchInt {
        discriminant: Operand,
        targets: Vec<SwitchTarget>,
        otherwise: u32,
    },
    UnwindResume,
    UnwindTerminate {
        reason: UnwindTerminateReason,
    },
    Return,
    Unreachable,
    Drop {
        place: Place,
        target: u32,
        unwind: Unwind,
        replace: bool,
        async_drop: Option<u32>,
    },
    Call {
        function: Operand,
        resolution: crate::resolution_values::Callee<C>,
        args: Vec<CallArgument>,
        destination: Place,
        target: Option<u32>,
        unwind: Unwind,
        call_source: CallSource,
        function_span: u64,
    },
    TailCall {
        function: Operand,
        resolution: crate::resolution_values::Callee<C>,
        args: Vec<CallArgument>,
        function_span: u64,
    },
    Assert {
        condition: Operand,
        expected: bool,
        message: AssertMessage,
        target: u32,
        unwind: Unwind,
    },
    Yield {
        value: Operand,
        resume: u32,
        resume_arg: Place,
        drop: Option<u32>,
    },
    CoroutineDrop,
    FalseEdge {
        real_target: u32,
        imaginary_target: u32,
    },
    FalseUnwind {
        real_target: u32,
        unwind: Unwind,
    },
    InlineAsm {
        asm_macro: &'static str,
        template: Vec<AsmPiece>,
        operands: Vec<AsmOperand>,
        options: AsmOptions,
        line_spans: Vec<u64>,
        targets: Vec<u32>,
        unwind: Unwind,
        execution_obligation: &'static str,
    },
}

#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum AsmRegister {
    Register {
        arch: Option<&'static str>,
        name: String,
    },
    RegisterClass {
        arch: Option<&'static str>,
        name: String,
    },
}
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum AsmPiece {
    String {
        text: String,
    },
    Placeholder {
        operand_index: usize,
        modifier: Option<String>,
        span: u64,
    },
}
#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum AsmOperand {
    In {
        register: AsmRegister,
        value: Operand,
    },
    Out {
        register: AsmRegister,
        late: bool,
        place: Option<Place>,
    },
    Inout {
        register: AsmRegister,
        late: bool,
        input: Operand,
        output: Option<Place>,
    },
    Const {
        value: crate::pool_constant::Operand,
    },
    SymFn {
        value: crate::pool_constant::Operand,
    },
    SymStatic {
        def_id: u64,
    },
    Label {
        target_index: usize,
    },
}
#[derive(Serialize)]
pub(super) struct AsmOptions {
    pub pure: bool,
    pub nomem: bool,
    pub readonly: bool,
    pub preserves_flags: bool,
    pub noreturn: bool,
    pub nostack: bool,
    pub att_syntax: bool,
    pub raw: bool,
    pub may_unwind: bool,
}

#[derive(Serialize)]
pub(super) struct Statement<Q = VtableQueryKey> {
    pub source_info: Shared<SourceInfo>,
    pub kind: Shared<StatementKind<Q>>,
}
#[derive(Serialize)]
pub(super) struct Terminator<C = crate::resolution_values::PendingCandidates> {
    pub source_info: Shared<SourceInfo>,
    pub kind: TerminatorKind<C>,
}
#[derive(Serialize)]
pub(super) struct BasicBlock<Q = VtableQueryKey, C = crate::resolution_values::PendingCandidates> {
    pub block: u32,
    pub is_cleanup: bool,
    pub statements: Vec<Statement<Q>>,
    pub terminator: Option<Terminator<C>>,
}
#[derive(Serialize)]
pub(super) struct Body<Q = VtableQueryKey, C = crate::resolution_values::PendingCandidates> {
    pub instance_id: u64,
    pub preamble_def_span: u64,
    pub backtrace_spans: Shared<Vec<BacktraceSpan>>,
    pub source_def_id: u64,
    pub phase: Phase,
    pub injection_phase: Option<Phase>,
    pub arg_count: usize,
    pub spread_arg: Option<u32>,
    pub span: u64,
    pub locals: Vec<Local>,
    pub basic_blocks: Vec<BasicBlock<Q, C>>,
    pub source_scopes: Vec<SourceScope>,
    pub required_consts: Vec<crate::pool_constant::Operand>,
}

#[derive(Serialize)]
pub(super) struct CopyTemplateSource {
    pub source_promoted: Option<u32>,
    pub template: String,
    pub source_def_id: u64,
    pub def_path: String,
    pub span: u64,
    pub preamble_def_span: u64,
    pub injection_phase: Option<Phase>,
    pub local_sources: Vec<SourceInfo>,
    pub source_scopes: Vec<SourceScope>,
    pub backtrace_spans: Vec<BacktraceSpan>,
}

#[derive(Serialize)]
#[serde(tag = "body_kind", rename_all = "snake_case")]
pub(super) enum BodySeed<Q = VtableQueryKey, C = crate::resolution_values::PendingCandidates> {
    Material { #[serde(flatten)] body: Body<Q,C> },
    NoopDrop {instance_id:u64, source_span:BacktraceSpan},
    FnPointerShim {instance_id:u64, source_span:BacktraceSpan,
        non_null_definition:u64, code_definition:u64},
    CopyTemplate {
        template_id: u64,
        instance_id: u64,
        generic_args: Vec<super::pool_values::GenericArgument>,
        promoted_bodies: Vec<super::pool_instance::PromotedBody>,
    },
}
impl BodySeed<VtableQueryKey,crate::resolution_values::PendingCandidates> {
    pub fn finish(self, ids:&std::collections::HashMap<(u64,Vec<u64>),u64>,
        candidates:&std::collections::HashMap<u64,Vec<u64>>) -> Result<BodySeed<u64,Vec<u64>>,String> {
        Ok(match self {
            Self::Material{body}=>BodySeed::Material{body:body.finish(ids,candidates)?},
            Self::NoopDrop{instance_id,source_span}=>BodySeed::NoopDrop{instance_id,source_span},
            Self::FnPointerShim{instance_id,source_span,non_null_definition,code_definition}=>
                BodySeed::FnPointerShim{instance_id,source_span,non_null_definition,code_definition},
            Self::CopyTemplate{template_id,instance_id,generic_args,promoted_bodies}=>
                BodySeed::CopyTemplate{template_id,instance_id,generic_args,promoted_bodies},
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn semantic_discriminants_preserve_wire_names() {
        assert_eq!(
            serde_json::to_value(DropHintReason::Edition2024).unwrap(),
            json!({"kind":"edition_2024"})
        );
        assert_eq!(
            serde_json::to_value(FakeReadCause::LetBinding { hoisted_from: None }).unwrap(),
            json!({"kind":"let_binding","hoisted_from":null})
        );
        assert_eq!(
            serde_json::to_value(Phase::Runtime {
                phase: RuntimePhase::PostCleanup
            })
            .unwrap(),
            json!({"kind":"runtime","phase":"post_cleanup"})
        );
    }

    #[test]
    fn intrinsic_discriminant_is_flattened_into_statement() {
        let statement = StatementKind::<u64>::Intrinsic {
            intrinsic: Intrinsic::Assume {
                value: Operand::RuntimeChecks {
                    check: RuntimeCheck::UbChecks { enabled: true },
                },
            },
        };
        assert_eq!(
            serde_json::to_value(statement).unwrap(),
            json!({"variant":"Intrinsic","intrinsic":"Assume","value":{"kind":"RuntimeChecks","check":{"kind":"ub_checks","enabled":true}}})
        );
    }
}

impl StatementKind<VtableQueryKey> {
    pub fn finish(
        self,
        ids: &std::collections::HashMap<(u64, Vec<u64>), u64>,
        candidates: &std::collections::HashMap<u64, Vec<u64>>,
    ) -> Result<StatementKind<u64>, String> {
        Ok(match self {
            Self::Assign { place, rvalue } => StatementKind::Assign {
                place: place,
                rvalue: rvalue.finish(ids, candidates)?,
            },
            Self::FakeRead { cause, place } => StatementKind::FakeRead {
                cause: cause,
                place: place,
            },
            Self::SetDiscriminant {
                place,
                variant_index,
            } => StatementKind::SetDiscriminant {
                place: place,
                variant_index: variant_index,
            },
            Self::StorageLive { local } => StatementKind::StorageLive { local: local },
            Self::StorageDead { local } => StatementKind::StorageDead { local: local },
            Self::PlaceMention { place } => StatementKind::PlaceMention { place: place },
            Self::AscribeUserType {
                execution,
                place,
                user_type_projection,
                variance,
            } => StatementKind::AscribeUserType {
                execution: execution,
                place: place,
                user_type_projection: user_type_projection,
                variance: variance,
            },
            Self::Coverage {
                execution,
                coverage,
            } => StatementKind::Coverage {
                execution: execution,
                coverage: coverage,
            },
            Self::Intrinsic { intrinsic } => StatementKind::Intrinsic {
                intrinsic: intrinsic,
            },
            Self::ConstEvalCounter => StatementKind::ConstEvalCounter,
            Self::Nop => StatementKind::Nop,
            Self::BackwardIncompatibleDropHint { place, reason } => {
                StatementKind::BackwardIncompatibleDropHint {
                    place: place,
                    reason: reason,
                }
            }
        })
    }
}

impl Rvalue<VtableQueryKey> {
    pub fn finish(
        self,
        ids: &std::collections::HashMap<(u64, Vec<u64>), u64>,
        _candidates: &std::collections::HashMap<u64, Vec<u64>>,
    ) -> Result<Rvalue<u64>, String> {
        Ok(match self {
            Self::Use { operand, retag } => Rvalue::Use {
                operand: operand,
                retag: retag,
            },
            Self::Repeat { operand, count } => Rvalue::Repeat {
                operand: operand,
                count: count,
            },
            Self::Ref {
                region,
                borrow_kind,
                place,
            } => Rvalue::Ref {
                region: region,
                borrow_kind: borrow_kind,
                place: place,
            },
            Self::ThreadLocalRef {
                global_info,
                def_id,
                def_path,
                initializer,
            } => Rvalue::ThreadLocalRef {
                global_info: global_info,
                def_id: def_id,
                def_path: def_path,
                initializer: initializer,
            },
            Self::RawPtr {
                pointer_kind,
                place,
            } => Rvalue::RawPtr {
                pointer_kind: pointer_kind,
                place: place,
            },
            Self::Cast {
                cast_kind,
                operand,
                target_type,
                vtable_allocation,
                vtable_query,
                vtable_probe,
            } => Rvalue::Cast {
                cast_kind: cast_kind,
                operand: operand,
                target_type: target_type,
                vtable_allocation: vtable_allocation,
                vtable_query: vtable_query.map(|query| query.finish(ids)).transpose()?,
                vtable_probe: vtable_probe,
            },
            Self::BinaryOp {
                operator,
                left,
                right,
                implicit_overflow_tuple_type,
            } => Rvalue::BinaryOp {
                operator: operator,
                left: left,
                right: right,
                implicit_overflow_tuple_type: implicit_overflow_tuple_type,
            },
            Self::UnaryOp { operator, operand } => Rvalue::UnaryOp {
                operator: operator,
                operand: operand,
            },
            Self::Discriminant { place } => Rvalue::Discriminant { place: place },
            Self::Aggregate {
                aggregate_kind,
                operands,
            } => Rvalue::Aggregate {
                aggregate_kind: aggregate_kind,
                operands: operands,
            },
            Self::CopyForDeref { place } => Rvalue::CopyForDeref { place: place },
            Self::WrapUnsafeBinder { operand, r#type } => {
                Rvalue::WrapUnsafeBinder { operand, r#type }
            }
            Self::Reborrow {
                r#type,
                mutability,
                place,
            } => Rvalue::Reborrow {
                r#type,
                mutability,
                place,
            },
        })
    }
}

impl Statement<VtableQueryKey> {
    pub fn finish(
        self,
        ids: &std::collections::HashMap<(u64, Vec<u64>), u64>,
        candidates: &std::collections::HashMap<u64, Vec<u64>>,
    ) -> Result<Statement<u64>, String> {
        Ok({
            let Self { source_info, kind } = self;
            Statement {
                source_info: source_info,
                kind: kind.try_map(|kind| kind.finish(ids, candidates))?,
            }
        })
    }
}

impl TerminatorKind<crate::resolution_values::PendingCandidates> {
    pub fn finish(
        self,
        _ids: &std::collections::HashMap<(u64, Vec<u64>), u64>,
        candidates: &std::collections::HashMap<u64, Vec<u64>>,
    ) -> Result<TerminatorKind<Vec<u64>>, String> {
        Ok(match self {
            Self::Goto { target, loop_hints } => TerminatorKind::Goto {
                target: target,
                loop_hints: loop_hints,
            },
            Self::SwitchInt {
                discriminant,
                targets,
                otherwise,
            } => TerminatorKind::SwitchInt {
                discriminant: discriminant,
                targets: targets,
                otherwise: otherwise,
            },
            Self::UnwindResume => TerminatorKind::UnwindResume,
            Self::UnwindTerminate { reason } => TerminatorKind::UnwindTerminate { reason: reason },
            Self::Return => TerminatorKind::Return,
            Self::Unreachable => TerminatorKind::Unreachable,
            Self::Drop {
                place,
                target,
                unwind,
                replace,
                async_drop,
            } => TerminatorKind::Drop {
                place: place,
                target: target,
                unwind: unwind,
                replace: replace,
                async_drop: async_drop,
            },
            Self::Call {
                function,
                resolution,
                args,
                destination,
                target,
                unwind,
                call_source,
                function_span,
            } => TerminatorKind::Call {
                function: function,
                resolution: resolution.finish(candidates),
                args: args,
                destination: destination,
                target: target,
                unwind: unwind,
                call_source: call_source,
                function_span: function_span,
            },
            Self::TailCall {
                function,
                resolution,
                args,
                function_span,
            } => TerminatorKind::TailCall {
                function: function,
                resolution: resolution.finish(candidates),
                args: args,
                function_span: function_span,
            },
            Self::Assert {
                condition,
                expected,
                message,
                target,
                unwind,
            } => TerminatorKind::Assert {
                condition: condition,
                expected: expected,
                message: message,
                target: target,
                unwind: unwind,
            },
            Self::Yield {
                value,
                resume,
                resume_arg,
                drop,
            } => TerminatorKind::Yield {
                value: value,
                resume: resume,
                resume_arg: resume_arg,
                drop: drop,
            },
            Self::CoroutineDrop => TerminatorKind::CoroutineDrop,
            Self::FalseEdge {
                real_target,
                imaginary_target,
            } => TerminatorKind::FalseEdge {
                real_target: real_target,
                imaginary_target: imaginary_target,
            },
            Self::FalseUnwind {
                real_target,
                unwind,
            } => TerminatorKind::FalseUnwind {
                real_target: real_target,
                unwind: unwind,
            },
            Self::InlineAsm {
                asm_macro,
                template,
                operands,
                options,
                line_spans,
                targets,
                unwind,
                execution_obligation,
            } => TerminatorKind::InlineAsm {
                asm_macro: asm_macro,
                template: template,
                operands: operands,
                options: options,
                line_spans: line_spans,
                targets: targets,
                unwind: unwind,
                execution_obligation: execution_obligation,
            },
        })
    }
}

impl Terminator<crate::resolution_values::PendingCandidates> {
    pub fn finish(
        self,
        ids: &std::collections::HashMap<(u64, Vec<u64>), u64>,
        candidates: &std::collections::HashMap<u64, Vec<u64>>,
    ) -> Result<Terminator<Vec<u64>>, String> {
        Ok({
            let Self { source_info, kind } = self;
            Terminator {
                source_info: source_info,
                kind: kind.finish(ids, candidates)?,
            }
        })
    }
}

impl BasicBlock<VtableQueryKey, crate::resolution_values::PendingCandidates> {
    pub fn finish(
        self,
        ids: &std::collections::HashMap<(u64, Vec<u64>), u64>,
        candidates: &std::collections::HashMap<u64, Vec<u64>>,
    ) -> Result<BasicBlock<u64, Vec<u64>>, String> {
        Ok({
            let Self {
                block,
                is_cleanup,
                statements,
                terminator,
            } = self;
            BasicBlock {
                block: block,
                is_cleanup: is_cleanup,
                statements: statements
                    .into_iter()
                    .map(|item| item.finish(ids, candidates))
                    .collect::<Result<_, String>>()?,
                terminator: terminator
                    .map(|item| item.finish(ids, candidates))
                    .transpose()?,
            }
        })
    }
}

impl Body<VtableQueryKey, crate::resolution_values::PendingCandidates> {
    pub fn finish(
        self,
        ids: &std::collections::HashMap<(u64, Vec<u64>), u64>,
        candidates: &std::collections::HashMap<u64, Vec<u64>>,
    ) -> Result<Body<u64, Vec<u64>>, String> {
        Ok({
            let Self {
                instance_id,
                preamble_def_span,
                backtrace_spans,
                source_def_id,
                phase,
                injection_phase,
                arg_count,
                spread_arg,
                span,
                locals,
                basic_blocks,
                source_scopes,
                required_consts,
            } = self;
            Body {
                instance_id,
                preamble_def_span: preamble_def_span,
                backtrace_spans: backtrace_spans,
                source_def_id: source_def_id,
                phase: phase,
                injection_phase: injection_phase,
                arg_count: arg_count,
                spread_arg: spread_arg,
                span: span,
                locals: locals,
                basic_blocks: basic_blocks
                    .into_iter()
                    .map(|item| item.finish(ids, candidates))
                    .collect::<Result<_, String>>()?,
                source_scopes: source_scopes,
                required_consts: required_consts,
            }
        })
    }
}

impl VtableQuery<VtableQueryKey> {
    fn finish(
        self,
        ids: &std::collections::HashMap<(u64, Vec<u64>), u64>,
    ) -> Result<VtableQuery<u64>, String> {
        let query_id = *ids
            .get(&(
                self.query_id.input_type_id,
                self.query_id.input_predicate_ids,
            ))
            .ok_or("vtable query is absent from the finalized compiler catalog")?;
        Ok(VtableQuery {
            source_type: self.source_type,
            target_type: self.target_type,
            source_pointee_type: self.source_pointee_type,
            target_pointee_type: self.target_pointee_type,
            input_type: self.input_type,
            input_predicates: self.input_predicates,
            source_tail_type: self.source_tail_type,
            target_tail_type: self.target_tail_type,
            query_id,
        })
    }
}
