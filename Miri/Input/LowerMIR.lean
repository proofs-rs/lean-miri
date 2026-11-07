import Miri.Input.CompilerTables
import Miri.Input.Model
import Miri.Input.Decoder
import Miri.MIR.Syntax

/-! Fail-closed bridge from decoded compiler data to the fixed interpreter AST.
Successful lowering is syntax construction, not execution readiness or UB freedom.
The original envelope and source scopes remain available beside the MIR body. -/
namespace Miri.Input

abbrev LowerResult := Except String

structure LowerContext where
  /-- Each supplied type ID must refer to this compilation's metadata graph. -/
  typeIds : Array TypeId
  /-- Exact byte widths from compiler layout metadata; required for scalar constants. -/
  scalarSizes : Array (Option Nat)
  allocationIds : Array AllocationId := #[]
  obligations : Array Obligation := #[]
  /-- Paired source for query metadata addressed by paths in decoded MIR. -/
  sourceDocument : Option Lean.Json := none
  validatedVtableProbeDiagnostics : Array String := #[]
  compilerValueMemo : Option CompilerValueMemo := none

/-- Consume complete import-time compiler values; manual contexts decode directly. -/
def LowerContext.decodeCompilerValue (ctx : LowerContext) (raw : Lean.Json) : Except String TypedValue :=
  decodeCompilerValueWithMemo raw ctx.compilerValueMemo

def LowerContext.containsTypeId (ctx : LowerContext) (id : TypeId) : Bool :=
  ctx.typeIds[id]? == some id

def LowerContext.containsAllocationId (ctx : LowerContext) (id : AllocationId) : Bool :=
  ctx.allocationIds[id]? == some id

def LowerContext.scalarSize (ctx : LowerContext) (id : TypeId) : Option Nat :=
  (ctx.scalarSizes[id]?).join

/-- Derive scalar widths from compiler metadata, never from bits or host types. -/
def LowerContext.ofTypes (types : Array TypeNode) (layouts : Miri.MIR.SharedTable Layout) : LowerContext := Id.run do
  let typeIds := types.map (·.id)
  let scalarSizes := types.map fun ty =>
    match layouts.lookup ty.layoutId with
    | .ok layout => if layout.status == .supported then layout.sizeBytes else none
    | .error _ => none
  let obligations : Array Obligation := types.filterMap fun ty =>
      if ty.shapeStatus == .supported then none else
        some ⟨s!"types[{ty.id}].shape", "type shape metadata remains unresolved; its compilation-local identity is preserved"⟩
  return {
    typeIds
    scalarSizes
    allocationIds := #[]
    obligations
    sourceDocument := none
  }

/-- Resolve graph identities from the same decoded compilation. Metadata
semantics remain independent from syntax lowering and its obligations. -/
def LowerContext.ofDocument (document : ImportDocumentCore) : LowerContext :=
  let ctx := ofTypes document.types document.layoutTable
  { ctx with
    allocationIds := document.allocations.map (·.id)
    sourceDocument := some document.raw
    validatedVtableProbeDiagnostics := document.validatedVtableProbeDiagnostics
    compilerValueMemo := document.compilerValueMemo }

set_option autoImplicit false in
/-- A prepared lowering context tied to one exact decoded source document.
The private constructor and equality field prevent reusing it for a different
document, even when the documents serialize to equal JSON. -/
structure LowerContext.Bound (document : ImportDocumentCore) where
  private mk ::
  value : LowerContext
  exact : value = LowerContext.ofDocument document

/-- Prepare the context and retain its exact document identity in the type. -/
def LowerContext.bindDocument (document : ImportDocumentCore) : LowerContext.Bound document :=
  ⟨LowerContext.ofDocument document, rfl⟩

structure LoweredBody where
  body : MIR.BodyNode
  bodyId : MIR.BodyId
  spans : Array SourceSpanData
  input : BodyCore
  definitions : Array DefinitionId
  typeConstants : Array MIR.TypeConst
  obligations : Array Obligation

/-- Resolve a crate-qualified compiler definition into this bundle's dense
identity. Raw rustc definition indices are never runtime definition IDs. -/
def lookupDefinitionId (definitions : Array DefinitionId) (sourceId : DefinitionId)
    : LowerResult MIR.DefId :=
  -- Compiler queries repeat this lookup; keep the search on the array rather
  -- than allocating a full list before examining the first matching ID.
  match definitions.idxOf? sourceId with
  | some id => pure id
  | none => throw s!"unresolved compiler definition {sourceId.crateIndex}:{sourceId.index}"

def LoweredBody.ownDefinitionId (body : LoweredBody) : LowerResult MIR.DefId := do
  let some sourceId := body.input.definitionId | throw "body is missing its source definition identity"
  lookupDefinitionId body.definitions sourceId

private structure LowerState where
  spans : Array SourceSpanData := #[]
  definitions : Array DefinitionId := #[]
  typeConstants : Array MIR.TypeConst := #[]
  /-- Buckets narrow equality checks without treating a hash as identity. -/
  spanCandidates : Option (Std.HashMap (String × Nat × Nat) (Array Nat)) := none
  definitionCandidates : Option (Std.HashMap (Nat × Nat) Nat) := none

private abbrev LowerM := StateT LowerState (Except String)
private abbrev Fields := Array (String × TypedValue)

private def get (fs : Fields) (key : String) : LowerResult TypedValue :=
  match fs.find? (fun entry => entry.1 == key) with
  | some (_, v) => .ok v
  | none => .error s!"missing lowering field {key}"

private def fields : TypedValue → LowerResult Fields
  | .object fs | .enumTag _ _ fs => .ok fs
  | _ => .error "expected typed object"

private def nat : TypedValue → LowerResult Nat
  | .scalar j => j.getNat?
  | .localRef n | .blockRef n => .ok n
  | _ => .error "expected unsigned integer"

private def bool : TypedValue → LowerResult Bool
  | .scalar j => j.getBool?
  | _ => .error "expected boolean"

private def text : TypedValue → LowerResult String
  | .scalar j => j.getStr?
  | _ => .error "expected string"

private def array : TypedValue → LowerResult (Array TypedValue)
  | .array vs => .ok vs
  | _ => .error "expected typed array"

private def tag : TypedValue → LowerResult String
  | .enumTag _ t _ => .ok t.tag
  | .object fs => get fs "kind" >>= text
  | v => text v

private def typeId (ctx : LowerContext) : TypedValue → LowerResult MIR.TyId
  | .typeRef id => if ctx.containsTypeId id then .ok id else .error s!"unresolved type {id}"
  | _ => .error "expected type reference"

private def spanCandidateKey (span : SourceSpanData) : String × Nat × Nat :=
  (span.file, span.lo, span.hi)

private def intern (span : SourceSpanData) : LowerM MIR.SpanRef := do
  let state ← StateT.get
  match state.spanCandidates with
  | none =>
    match state.spans.toList.idxOf? span with
    | some i => pure ⟨i⟩
    | none =>
      StateT.set { state with spans := state.spans.push span }
      pure ⟨state.spans.size⟩
  | some candidates =>
    let bucket := candidates.getD (spanCandidateKey span) #[]
    if let some i := bucket.find? fun i =>
        match state.spans[i]? with
        | some previous => decide (previous = span)
        | none => false then
      pure ⟨i⟩
    else
      let i := state.spans.size
      let nextCandidates := candidates.insert (spanCandidateKey span) (bucket.push i)
      StateT.set { state with spans := state.spans.push span, spanCandidates := some nextCandidates }
      pure ⟨i⟩

private def optional (lower : TypedValue → LowerResult α) : TypedValue → LowerResult (Option α)
  | .scalar .null => pure none
  | value => some <$> lower value

private def number (v : TypedValue) : LowerResult Nat := do
  match v with
  | .scalar (.str s) => match s.toNat? with | some n => pure n | none => throw "invalid decimal integer"
  | v => nat v

private def definition (v : TypedValue) : LowerM MIR.DefId := do
  let id ← (show LowerM DefinitionId from match v with
    | .object fs => return DefinitionId.mk (← nat (← get fs "crate")) (← nat (← get fs "index"))
    | v => do
      let encoded ← text v
      match encoded.splitOn ":" with
      | [cratePart, indexPart] =>
        match cratePart.toNat?, indexPart.toNat? with
        | some c, some i => pure (DefinitionId.mk c i)
        | _, _ => throw "invalid compiler definition ID"
      | _ => throw "expected crate-qualified definition ID")
  let state ← StateT.get
  let key := (id.crateIndex,id.index)
  let found := match state.definitionCandidates with
    | some candidates => candidates.get? key
    | none => state.definitions.toList.idxOf? id
  match found with
  | some i => pure i
  | none =>
    let i := state.definitions.size
    let candidates := state.definitionCandidates.map (·.insert key i)
    StateT.set { state with definitions := state.definitions.push id, definitionCandidates := candidates }
    pure i

private def spanRef : TypedValue → LowerM MIR.SpanRef
  | .sourceSpan span => intern span
  | _ => throw "missing typed source span"

private def boundIndex (v : TypedValue) : LowerResult MIR.BoundVarIndexKind := do
  let fs ← fields v
  match ← tag v with
  | "bound" => return .Bound (← nat (← get fs "debruijn_index"))
  | "canonical" => pure .Canonical
  | _ => throw "unknown bound index kind"

private def boundRegion (v : TypedValue) : LowerM MIR.BoundRegionKind := do
  let fs ← fields v
  match ← tag v with
  | "anonymous" => pure .Anon
  | "named_for_printing" => return .NamedForPrinting (← text (← get fs "name"))
  | "named" => return .Named (← definition (← get fs "def_id"))
  | "closure_environment" => pure .ClosureEnv
  | _ => throw "unknown bound region kind"

private def region (v : TypedValue) : LowerM MIR.Region := do
  let fs ← fields v
  match ← tag v with
  | "early_parameter" => return .EarlyParameter (← nat (← get fs "index")) (← text (← get fs "name"))
  | "bound" => return .Bound (← boundIndex (← get fs "index_kind")) (← nat (← get fs "variable_index")) (← boundRegion (← get fs "bound_kind"))
  | "late_parameter" =>
    let p ← get fs "parameter"
    let pf ← fields p
    let kind ← (show LowerM MIR.LateParamRegionKind from match ← tag p with
      | "anonymous" => return .Anon (← nat (← get pf "index"))
      | "named_anonymous" => return .NamedAnon (← nat (← get pf "index")) (← text (← get pf "name"))
      | "named" => return .Named (← definition (← get pf "def_id"))
      | "closure_environment" => pure .ClosureEnv
      | _ => throw "unknown late parameter region")
    return .LateParameter (← definition (← get fs "scope_def_id")) kind
  | "static" => pure .Static
  | "inference_variable" => return .InferenceVariable (← nat (← get fs "index"))
  | "placeholder" => return .Placeholder (← nat (← get fs "universe")) (← nat (← get fs "variable_index")) (← boundRegion (← get fs "bound_kind"))
  | "erased" => pure .Erased
  | "error" => pure .Error
  | _ => throw "unknown region"

private def binOp (v : TypedValue) : LowerResult MIR.BinOp := do
  match v with
  | .binOperator op .supported => pure op
  | _ =>
    match ← tag v with
    | "add" => pure .Add
    | "add_unchecked" => pure .AddUnchecked
    | "add_with_overflow" => pure .AddWithOverflow
    | "sub" => pure .Sub
    | "sub_unchecked" => pure .SubUnchecked
    | "sub_with_overflow" => pure .SubWithOverflow
    | "mul" => pure .Mul
    | "mul_unchecked" => pure .MulUnchecked
    | "mul_with_overflow" => pure .MulWithOverflow
    | "div" => pure .Div
    | "rem" => pure .Rem
    | "bit_xor" => pure .BitXor
    | "bit_and" => pure .BitAnd
    | "bit_or" => pure .BitOr
    | "shift_left" => pure .Shl
    | "shift_left_unchecked" => pure .ShlUnchecked
    | "shift_right" => pure .Shr
    | "shift_right_unchecked" => pure .ShrUnchecked
    | "equal" => pure .Eq
    | "less_than" => pure .Lt
    | "less_equal" => pure .Le
    | "not_equal" => pure .Ne
    | "greater_equal" => pure .Ge
    | "greater_than" => pure .Gt
    | "compare" => pure .Cmp
    | "pointer_offset" => pure .Offset
    | _ => throw "unknown binary operator"

private def unOp (v : TypedValue) : LowerResult MIR.UnOp := do
  match v with
  | .unOperator op .supported => pure op
  | _ =>
    match ← tag v with
    | "not" => pure .Not
    | "negate" => pure .Neg
    | "pointer_metadata" => pure .PtrMetadata
    | _ => throw "unknown unary operator"

private def internTypeConst (constant : MIR.TypeConst) : LowerM MIR.TypeConstId := do
  let state ← StateT.get
  match state.typeConstants.toList.idxOf? constant with
  | some i => pure i
  | none =>
    StateT.set { state with typeConstants := state.typeConstants.push constant }
    pure state.typeConstants.size

mutual
private partial def typeConst (ctx : LowerContext) (v : TypedValue) : LowerM MIR.TypeConst := do
  let fs ← fields v
  match ← tag v with
  | "parameter" =>
    let declared ← get fs "declared_type"
    let declared ← match declared with
      | .typeRef id => some <$> typeId ctx (.typeRef id)
      | .scalar .null => pure none
      | .object metadata =>
        match ← text (← get metadata "status") with
        | "unknown" => pure none
        | _ => throw "invalid parameter declared type metadata"
      | _ => throw "unresolved parameter declared type metadata"
    return .Param (← nat (← get fs "index")) (← text (← get fs "name")) declared
  | "inference" =>
    let infer ← get fs "inference"
    let inf ← fields infer
    match ← tag infer with
    | "variable" => return .InferVar (← nat (← get inf "index"))
    | "fresh" => return .InferFresh (← nat (← get inf "index"))
    | _ => throw "unknown const inference"
  | "bound" => return .Bound (← boundIndex (← get fs "index_kind")) (← nat (← get fs "variable_index"))
  | "placeholder" => return .Placeholder (← nat (← get fs "universe")) (← nat (← get fs "variable_index"))
  | "alias" =>
    let kind ← (show LowerM MIR.ConstAliasKind from match ← text (← get fs "alias_kind") with
      | "projection" => pure .Projection
      | "inherent_self" => pure .InherentSelf
      | "inherent_impl" => pure .InherentImpl
      | "free" => pure .Free
      | "anonymous" => pure .Anon
      | _ => throw "unknown const alias kind")
    let rigid ← match ← text (← get fs "rigidity") with
      | "rigid" => pure true
      | "not_rigid" => pure false
      | _ => throw "unknown const rigidity"
    return .Alias rigid kind (← definition (← get fs "def_id")) (← genericArgs ctx (← get fs "generic_args"))
  | "value" => return .Value (← typeId ctx (← get fs "type")) (← valTree ctx (← get fs "value"))
  | "error" => pure .Error
  | "expression" =>
    let kind ← (show LowerM MIR.ConstExpressionKind from match ← text (← get fs "expression_kind") with
      | "binary_operator" => return .Binop (← binOp (← get fs "operator"))
      | "unary_operator" => return .UnOp (← unOp (← get fs "operator"))
      | "function_call" => pure .FunctionCall
      | "cast" => do
        match ← text (← get fs "operator") with
        | "as" => pure (.Cast .As)
        | "use" => pure (.Cast .Use)
        | _ => throw "unknown abstract const cast"
      | _ => throw "unknown const expression")
    return .Expr kind (← genericArgs ctx (← get fs "arguments"))
  | _ => throw "unknown type constant"

private partial def genericArgs (ctx : LowerContext) (v : TypedValue) : LowerM (Array MIR.GenericArg) := do
  (← array v).mapM fun arg => do
    let fs ← fields arg
    match ← tag arg with
    | "type" => return .Type (← typeId ctx (← get fs "value"))
    | "lifetime" => return .Lifetime (← region (← get fs "value"))
    | "const" => return .Const (← internTypeConst (← typeConst ctx (← get fs "value")))
    | _ => throw "unknown generic argument"

private partial def valTree (ctx : LowerContext) (v : TypedValue) : LowerM MIR.ValTree := do
  let fs ← fields v
  match ← tag v with
  | "leaf" =>
    let size ← nat (← get fs "size_bytes")
    let bits ← number (← get fs "bits_unsigned")
    unless size > 0 && bits < 2 ^ (size * 8) do throw "invalid valtree scalar width"
    pure ⟨#[.Leaf bits size], 0⟩
  | "branch" =>
    let children ← (← array (← get fs "elements")).mapM fun child => do
      internTypeConst (← typeConst ctx child)
    pure ⟨#[.Branch children], 0⟩
  | _ => throw "unknown valtree"
end

private def annotation (v : TypedValue) : LowerResult Nat := do
  match v with
  | .scalar (.num _) => nat v
  | _ => let fs ← fields v; nat (← get fs "index")

private def allocationId (ctx : LowerContext) : TypedValue → LowerResult MIR.AllocationId
  | .allocationRef id => if ctx.containsAllocationId id then pure id else throw s!"unresolved allocation {id}"
  | _ => throw "unresolved allocation reference"

private def constValue (ctx : LowerContext) (ty : MIR.TyId) (v : TypedValue) : LowerResult MIR.ConstValue := do
  let fs ← fields v
  match ← tag v with
  | "zero_sized" => pure .ZeroSized
  | "scalar" =>
    let bits ← number (← get fs "bits_unsigned")
    let size ← match ctx.scalarSize ty with
      | some size => pure size
      | none => throw s!"missing scalar byte width for type {ty}"
    unless size > 0 && bits < 2 ^ (8 * size) do throw "scalar bits exceed byte width"
    pure (.Scalar (.Int bits size))
  | "pointer_scalar" => return .Scalar (.Ptr (.Allocation (← allocationId ctx (← get fs "allocation")) (← nat (← get fs "offset_bytes")) (← bool (← get fs "immutable")) (← bool (← get fs "shared_ref"))))
  | "pointer_scalar_without_provenance" => return .Scalar (.Ptr (.Address (← number (← get fs "address")) (← nat (← get fs "address_width_bytes"))))
  | "slice_allocation" => return .Slice (← allocationId ctx (← get fs "allocation")) (← nat (← get fs "metadata_length"))
  | "indirect_allocation" => return .Indirect (← allocationId ctx (← get fs "allocation")) (← nat (← get fs "offset_bytes"))
  | _ => throw "unknown or unavailable evaluated constant"

private def constOperand (ctx : LowerContext) (v : TypedValue) : LowerM MIR.ConstOperand := do
  let c ← fields v
  let ty ← typeId ctx (← get c "type")
  let userType ← optional annotation (← get c "user_type_annotation")
  let span ← spanRef (← get c "span")
  let evaluated ← fields (← get c "constant")
  let originalValue ← get evaluated "source"
  let original ← fields originalValue
  let constant ← (show LowerM MIR.MirConst from match ← tag originalValue with
    | "already_evaluated" => return .Val (← constValue ctx ty (← get evaluated "value")) ty
    | "type_system_const" => return .Ty (← typeId ctx (← get original "type")) (← typeConst ctx (← get original "const"))
    | "unevaluated" => return .Unevaluated ⟨← definition (← get original "def_id"), ← genericArgs ctx (← get original "generic_args"), ← optional nat (← get original "promoted")⟩ (← typeId ctx (← get original "type"))
    | _ => throw "unknown MIR constant source")
  pure ⟨span, userType, constant⟩


structure LoweredBodies where
  bodies : Array LoweredBody
  spans : Array SourceSpanData
  definitions : Array DefinitionId
  typeConstants : Array MIR.TypeConst

structure LoweredProgram where
  bundle : LoweredBodies
  /-- Root body indices into `bundle.bodies`, in the original document order. -/
  roots : Array Nat
  /-- Instance graph identity to body index; the source graph is retained below. -/
  instances : Array (InstanceId × Nat)
  /-- (parent body index, promoted index, body index). -/
  promoted : Array (Nat × Nat × Nat)
  input : ImportDocumentCore

/-- Look up a document root's frame identity without assuming it was called
or that source and runtime definition indices coincide. -/
def LoweredProgram.rootDefinitionId (program : LoweredProgram) (rootIndex : Nat)
    : LowerResult MIR.DefId := do
  let some bodyIndex := program.roots[rootIndex]? | throw "root index is out of range"
  let some body := program.bundle.bodies[bodyIndex]? | throw "root body index is out of range"
  body.ownDefinitionId

/-- Lower all present root, instance, and promoted bodies with global compiler
identity tables. Unavailable bodies remain explicit source graph obligations. -/
def lowerCoreProgram (input : ImportDocumentCore) : LowerResult LoweredProgram := do
  let mut inputs : Array BodyCore := #[]
  let mut roots := #[]
  let mut instances := #[]
  let mut promoted := #[]
  for body in input.bodies do
    let parent := inputs.size
    roots := roots.push parent
    inputs := inputs.push body.toBodyCore
    for child in body.promotedBodies do
      if let some childBody := child.body then
        promoted := promoted.push (parent, child.index, inputs.size)
        inputs := inputs.push childBody
  for inst in input.instances do
    if let some body := inst.body then
      let parent := inputs.size
      instances := instances.push (inst.id, parent)
      inputs := inputs.push body.toBodyCore
      let children := if body.promotedBodies.isEmpty then inst.promotedBodies else body.promotedBodies
      for child in children do
        if let some childBody := child.body then
          promoted := promoted.push (parent, child.index, inputs.size)
          inputs := inputs.push childBody
  -- The complete source body list includes root/instance/promoted identities;
  -- seed all of them explicitly, plus graph instances that have no MIR body.
  unless input.mirTables.bodies.size == inputs.size do throw "MIR body table does not match source body catalog"
  let tables := input.mirTables.compiler
  let ctx := LowerContext.ofDocument input
  let mut bodies := #[]
  for (source,index) in inputs.toList.zipIdx do
    let bodyId ← input.mirTables.bodyId index
    let body ← input.mirTables.body index
    let mut obligations := ctx.obligations
    match source.syntaxObligations with
    | some extracted => obligations := obligations ++ extracted
    | none =>
      for (block,blockIndex) in source.blocks.toList.zipIdx do
        let bodyPath := if source.sourcePath.isEmpty then "" else source.sourcePath ++ "."
        let path := s!"{bodyPath}basic_blocks[{blockIndex}]"
        for (node,statementIndex) in block.statements.toList.zipIdx do
          obligations := obligations ++ DecoderValues.syntaxPayloadObligations ctx.validatedVtableProbeDiagnostics.contains node.value s!"{path}.statements[{statementIndex}].kind"
        obligations := obligations ++ DecoderValues.syntaxPayloadObligations ctx.validatedVtableProbeDiagnostics.contains block.terminator.value s!"{path}.terminator.kind"
    unless source.definitionId.isSome do
      obligations := obligations.push ⟨"body.definitionId", "source definition identity is missing"⟩
    bodies := bodies.push {
      body, bodyId, input := source, obligations
      spans := tables.spans, definitions := tables.definitions, typeConstants := tables.typeConstants }
  pure ⟨⟨bodies, tables.spans, tables.definitions, tables.typeConstants⟩, roots, instances, promoted, input⟩


def lowerProgram (input : ImportDocument) : LowerResult LoweredProgram :=
  lowerCoreProgram input.toCore

def LoweredProgram.compilerTables (program : LoweredProgram) : CompilerTables :=
  ⟨program.bundle.spans, program.bundle.definitions, program.bundle.typeConstants⟩

def LoweredProgram.withCompilerTables (program : LoweredProgram) (tables : CompilerTables) : LoweredProgram :=
  let bodies := program.bundle.bodies.map fun body => { body with
    spans := tables.spans, definitions := tables.definitions, typeConstants := tables.typeConstants }
  { program with bundle := ⟨bodies, tables.spans, tables.definitions, tables.typeConstants⟩ }

def lowerCompilerGenericArgs (ctx : LowerContext) (tables : CompilerTables) (value : TypedValue) :
    LowerResult (Array MIR.GenericArg × CompilerTables) := do
  let (args, state) ← (genericArgs ctx value).run
    { spans := tables.spans, definitions := tables.definitions, typeConstants := tables.typeConstants }
  pure (args, ⟨state.spans, state.definitions, state.typeConstants⟩)

def lowerCompilerConstOperand (ctx : LowerContext) (tables : CompilerTables) (value : TypedValue) :
    LowerResult (MIR.ConstOperand × CompilerTables) := do
  let (operand, state) ← (constOperand ctx value).run
    { spans := tables.spans, definitions := tables.definitions, typeConstants := tables.typeConstants }
  pure (operand, ⟨state.spans, state.definitions, state.typeConstants⟩)

def lowerCompilerConstValue (ctx : LowerContext) (ty : MIR.TyId) (value : TypedValue) :
    LowerResult MIR.ConstValue := constValue ctx ty value

/-- Canonical type-constant interning for compiler pattern/query metadata. -/
def lowerCompilerTypeConst (ctx : LowerContext) (tables : CompilerTables) (value : TypedValue) :
    LowerResult (MIR.TypeConstId × CompilerTables) := do
  let (id, state) ← (do internTypeConst (← typeConst ctx value)).run
    { spans := tables.spans, definitions := tables.definitions, typeConstants := tables.typeConstants }
  pure (id, ⟨state.spans, state.definitions, state.typeConstants⟩)

/-- Intern a compiler span without synthesizing a source location. -/
def lowerCompilerSpan (tables : CompilerTables) (value : TypedValue) :
    LowerResult (MIR.SpanRef × CompilerTables) := do
  let (id, state) ← (spanRef value).run
    { spans := tables.spans, definitions := tables.definitions, typeConstants := tables.typeConstants }
  pure (id, ⟨state.spans, state.definitions, state.typeConstants⟩)

private structure SpanArrayReflexivity (spans : Array SourceSpanData) where
  reflexive : (spans == spans) = true

private theorem SpanArrayReflexivity.prepare
    (spans : Array SourceSpanData) : SpanArrayReflexivity spans :=
  ⟨by simp⟩

private def SpanArrayReflexivity.matchesRight
    {spans : Array SourceSpanData}
    (certificate : SpanArrayReflexivity spans)
    (candidate : Array SourceSpanData) : Bool :=
  withPtrEq spans candidate (fun _ => spans == candidate)
    (by intro equal; cases equal; exact certificate.reflexive)

private theorem SpanArrayReflexivity.matchesRight_eq
    {spans : Array SourceSpanData}
    (certificate : SpanArrayReflexivity spans)
    (candidate : Array SourceSpanData) :
    certificate.matchesRight candidate = (spans == candidate) := by
  simp [matchesRight, withPtrEq]

/-- Incremental exact span interning for compiler source-map batches. The
candidate index is seeded once from the existing table; buckets only narrow
the search and full span equality remains authoritative. -/
structure CompilerSpanInterner where
  private mk ::
  private tables : CompilerTables
  private candidates : Std.HashMap (String × Nat × Nat) (Array Nat)
  private spanReflexivity : SpanArrayReflexivity tables.spans

def CompilerSpanInterner.ofTables (tables : CompilerTables) : CompilerSpanInterner := Id.run do
  let mut candidates : Std.HashMap (String × Nat × Nat) (Array Nat) := {}
  for index in [:tables.spans.size] do
    if let some span := tables.spans[index]? then
      let key := spanCandidateKey span
      candidates := candidates.insert key ((candidates.getD key #[]).push index)
  return ⟨tables, candidates, .prepare tables.spans⟩

/-- Reuse an index only when the complete span arrays compare equal. The
certificate makes the common same-array case constant time while preserving a
full equality check for independently allocated or reordered tables. -/
def CompilerSpanInterner.rebind (interner : CompilerSpanInterner) (tables : CompilerTables) :
    CompilerSpanInterner :=
  if interner.spanReflexivity.matchesRight tables.spans then
    ⟨{ tables with spans := interner.tables.spans }, interner.candidates,
      interner.spanReflexivity⟩
  else
    .ofTables tables

def CompilerSpanInterner.getTables (interner : CompilerSpanInterner) : CompilerTables :=
  interner.tables

def lowerCompilerSpanWithInterner (interner : CompilerSpanInterner) (value : TypedValue) :
    LowerResult (MIR.SpanRef × CompilerSpanInterner) := do
  let (id, state) ← (spanRef value).run
    { spans := interner.tables.spans
      definitions := interner.tables.definitions
      typeConstants := interner.tables.typeConstants
      spanCandidates := some interner.candidates }
  let tables : CompilerTables := ⟨state.spans, state.definitions, state.typeConstants⟩
  return (id, ⟨tables, state.spanCandidates.getD interner.candidates,
    .prepare state.spans⟩)

/-- Compare the result of an independent lowering against the unchanged base.
The checked pointer shortcut retains the full original array comparator. -/
def CompilerSpanInterner.sameSpansAs (result base : CompilerSpanInterner) : Bool :=
  base.spanReflexivity.matchesRight result.tables.spans

theorem CompilerSpanInterner.sameSpansAs_eq (result base : CompilerSpanInterner) :
    result.sameSpansAs base = (base.getTables.spans == result.getTables.spans) := by
  exact base.spanReflexivity.matchesRight_eq result.tables.spans

/-- Lower a compiler constant operand using an exact, persistent span index. -/
def lowerCompilerConstOperandWithInterner (ctx : LowerContext)
    (interner : CompilerSpanInterner) (value : TypedValue) :
    LowerResult (MIR.ConstOperand × CompilerSpanInterner) := do
  let (operand, state) ← (constOperand ctx value).run
    { spans := interner.tables.spans
      definitions := interner.tables.definitions
      typeConstants := interner.tables.typeConstants
      spanCandidates := some interner.candidates }
  let tables : CompilerTables := ⟨state.spans, state.definitions, state.typeConstants⟩
  return (operand, ⟨tables, state.spanCandidates.getD interner.candidates,
    .prepare state.spans⟩)

end Miri.Input
