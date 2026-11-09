//! Semantic MIR body metadata. References are exporter-local pool indices.
use serde::Serialize;

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

pub(super) use crate::pool_values::DebugPayload;

#[derive(Clone, Debug, Serialize)]
pub(super) struct SourcePosition {
    pub byte_position: u32,
    pub line: usize,
    pub zero_based_char_column: usize,
    pub filename: String,
}

#[derive(Clone, Debug, Serialize)]
pub(super) struct BacktraceSpan {
    pub span: u64,
    pub collapsed_lo: u32,
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
    pub local_data: DebugPayload,
}

#[derive(Clone, Debug, Serialize)]
pub(super) struct Local {
    pub local: u32,
    pub mutability: Mutability,
    pub r#type: u64,
    pub layout: u64,
    pub source_info: SourceInfo,
    pub local_info: DebugPayload,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub(super) enum Mutability {
    Mutable,
    Immutable,
}

#[derive(Clone, Debug, Serialize)]
pub(super) struct Normalization {
    pub body: usize,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "snake_case")]
pub(super) enum InputPhase {
    Template,
    AlreadyInstantiated,
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
pub(super) enum StatementKind {
    Assign {
        place: Place,
        rvalue: Rvalue,
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
pub(super) enum Rvalue {
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
        vtable_query: Option<VtableQuery>,
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
pub(super) struct VtableQuery {
    pub source_type: u64,
    pub target_type: u64,
    pub source_pointee_type: u64,
    pub target_pointee_type: u64,
    pub input_type: u64,
    pub input_predicates: Vec<u64>,
    pub source_tail_type: u64,
    pub target_tail_type: u64,
    pub _query_key: VtableQueryKey,
}
#[derive(Serialize)]
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
pub(super) enum TerminatorKind {
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
        resolution: crate::resolution_values::Callee,
        args: Vec<CallArgument>,
        destination: Place,
        target: Option<u32>,
        unwind: Unwind,
        call_source: CallSource,
        function_span: u64,
    },
    TailCall {
        function: Operand,
        resolution: crate::resolution_values::Callee,
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
pub(super) struct Statement {
    pub source_info: SourceInfo,
    pub kind: StatementKind,
}
#[derive(Serialize)]
pub(super) struct Terminator {
    pub source_info: SourceInfo,
    pub kind: TerminatorKind,
}
#[derive(Serialize)]
pub(super) struct BasicBlock {
    pub block: u32,
    pub is_cleanup: bool,
    pub statements: Vec<Statement>,
    pub terminator: Option<Terminator>,
}
#[derive(Serialize)]
pub(super) struct ConstantQueryContext {
    pub instance_id: u64,
    pub mir_input_phase: InputPhase,
    pub required_constant_checks: crate::pool_constant::RequiredConstantChecks,
    pub normalization: Normalization,
}
#[derive(Serialize)]
pub(super) struct Body {
    pub source_instance_kind: crate::pool_instance::InstanceKind,
    pub preamble_def_span: u64,
    pub backtrace_spans: Vec<BacktraceSpan>,
    pub source_def_id: u64,
    pub source_promoted: Option<u32>,
    pub phase: Phase,
    pub pass_count: usize,
    pub is_polymorphic: bool,
    pub source_body_is_polymorphic: bool,
    pub injection_phase: Option<Phase>,
    pub tainted_by_errors: Option<crate::pool_values::DebugPayload>,
    pub arg_count: usize,
    pub spread_arg: Option<u32>,
    pub span: u64,
    pub locals: Vec<Local>,
    pub basic_blocks: Vec<BasicBlock>,
    pub source_scopes: Vec<SourceScope>,
    pub var_debug_info: Vec<crate::pool_values::DebugPayload>,
    pub mentioned_items: Option<crate::pool_values::DebugPayload>,
    pub required_consts: Option<Vec<crate::pool_constant::Operand>>,
    pub user_type_annotations: crate::pool_values::DebugPayload,
    pub coroutine_info: Option<CoroutineInfo>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub constant_query_context: Option<ConstantQueryContext>,
}
// Coroutine bodies fail export before a Body is constructed.
#[derive(Serialize)]
pub(super) enum CoroutineInfo {}

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
        let statement = StatementKind::Intrinsic {
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
