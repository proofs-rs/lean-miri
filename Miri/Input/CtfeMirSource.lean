import Miri.Input.RawU64Frame
import Miri.Input.CompilerBodyRole
import Miri.Input.CompilerTypingEnv
import Miri.Interpreter.CompileTime.ScalarFrame
import Miri.Interpreter.CompileTime.SourceStack

/-! Raw CTFE scalar-frame source, distinct from runtime MIR and query answers.
The accepted policy retains primitive source types/values and source locations;
it does not authorize whole constant-query evaluation or compiler allocation. -/
namespace Miri.Input.CtfeMirSource
open GenericSubstitution Miri.MIR
open Miri.Interpreter.CompileTime
inductive Policy where
  | scalarU32 | scalarU32CallsV1 | scalarU32ConstArgsV1 | rawU64
  deriving Repr, DecidableEq
structure LintRoot where
  owner : DefinitionIdentity
  localId : Nat
  deriving Repr, DecidableEq
structure Scope where
  span : SpanRef
  parent : Option Nat
  lintRoot : Option LintRoot
  deriving Repr, DecidableEq
/-- Policies carry disjoint typed programs; old scalar consumers must dispatch. -/
inductive Program where
  | rawU64 (value : RawU64Frame.Program)
  | scalar (value : ScalarFrame.Program)
  | calls (value : SourceStack.Source)
  deriving Repr, DecidableEq

structure Source where
  definition : DefinitionIdentity
  role : CompilerBodyRole
  promoted : Option Nat
  policy : Policy
  phase : MirPhase
  environment : CompilerTypingEnv.Recipe
  parameters : Array ArgSort
  requiredConstants : Array ScalarFrame.Operand
  span : SpanRef
  program : Program
  localSources : Array SourceInfo
  localMutability : Array Bool
  statementSources : Array (Array SourceInfo)
  terminatorSources : Array SourceInfo
  scopes : Array Scope
  deriving Repr, DecidableEq

/-- Lossless scalar-policy embedding for a source-only stack. It does not
reclassify the wire policy or grant a query-result capability. -/
def scalarProgram (program : ScalarFrame.Program) : CallFrame.Program := Id.run do
  let rec ty : ScalarFrame.Ty → CallFrame.Ty
    | .uint bits => .uint bits | .boolean => .boolean | .unit => .unit | .never => .never
    | .pair a b => .pair (ty a) (ty b)
  let rec value : ScalarFrame.Value → CallFrame.Value
    | .uint bits n => .uint bits n | .boolean b => .boolean b | .unit => .unit
    | .uninitialized t => .uninitialized (ty t) | .pair a b => .pair (value a) (value b)
  let place (p : ScalarFrame.Place) : CallFrame.Place := ⟨p.slot,p.fields⟩
  let operand : ScalarFrame.Operand → CallFrame.Operand
    | .copy p => .copy (place p) | .move p => .move (place p)
    | .sourceValue s => .sourceValue ⟨match s.kind with | .typeValue => .typeValue | .literalValue => .literalValue,s.span,s.userType,value s.value⟩
  let binary : ScalarFrame.Binary → CallFrame.Binary
    | .gt => .gt | .addWithOverflow => .addWithOverflow | .subWithOverflow => .subWithOverflow
  let rvalue : ScalarFrame.Rvalue → CallFrame.Rvalue
    | .use v retag => .use (operand v) retag
    | .binary kind a b => .binary (binary kind) (operand a) (operand b)
  let statement : ScalarFrame.Statement → CallFrame.Statement
    | .live n => .live n | .dead n => .dead n | .counter => .counter | .nop => .nop
    | .assign p v => .assign (place p) (rvalue v)
  let message : ScalarFrame.AssertMessage → CallFrame.AssertMessage
    | .overflow kind a b => .overflow (match kind with | .add => .add | .sub => .sub) (operand a) (operand b)
  let terminator : ScalarFrame.Terminator → CallFrame.Terminator
    | .goto n => .goto n | .switch v cases otherwise => .switch (operand v) cases otherwise
    | .assert v expected msg target => .assert (operand v) expected (message msg) target
    | .ret => .ret
  return ⟨program.locals.map ty,program.argumentCount,program.blocks.map fun b => ⟨b.statements.map statement,terminator b.terminator⟩⟩

/-- The stack's physical indices have an explicit local-crate universe. -/
def stackSource (source : Source) : Except String SourceStack.Source := do
  unless source.definition.crateIndex == 0 && source.promoted.isNone do
    throw "source stack requires unpromoted local crate0 identity"
  match source.program with
  | .rawU64 _ => throw "physical u64 source requires the typed CTFE root provider"
  | .calls program => pure program
  | .scalar program =>
    unless source.requiredConstants.isEmpty do throw "scalar embedding requires empty preamble"
    pure {
      definition := source.definition.index,name := "",required := #[]
      typeParameters := source.parameters.size,program := scalarProgram program
      cleanup := program.blocks.map (fun _ => false)}

def validate (source : Source) : Except String Unit := do
  unless source.role == .ctfe do throw "CTFE source requires the CTFE compiler body role"
  unless source.phase == .Runtime .PostCleanup do throw "scalar CTFE source has wrong MIR acquisition phase"
  unless source.environment == .declaration source.definition .postAnalysis do
    throw "CTFE source declaration environment recipe contradicts its source owner/mode"
  unless source.parameters.all (· != .aggregate) do throw "invalid CTFE declaration parameter sort"
  if source.policy == .rawU64 then
    let .rawU64 program := source.program | throw "raw u64 policy/program mismatch"
    unless source.parameters.isEmpty && source.promoted.isNone && source.requiredConstants.isEmpty do
      throw "raw u64 frame header/preamble domain mismatch"
    RawU64Frame.validate program
    unless source.localSources.size == program.localCount && source.localMutability.size == program.localCount &&
        source.statementSources.size == 1 && source.terminatorSources.size == 1 do throw "raw u64 frame source-info domain mismatch"
    let some statements := source.statementSources[0]? | throw "raw u64 frame source block absent"
    unless statements.size == program.statements.size do throw "raw u64 frame statement source-info mismatch"
    for value in source.localSources ++ statements ++ source.terminatorSources do
      unless value.scope < source.scopes.size do throw "raw u64 frame source scope absent"
    for (scope,index) in source.scopes.zipIdx do
      if let some parent := scope.parent then
        unless parent < index do throw "raw u64 scope parent is not earlier"
    return ()
  let program ← match source.policy,source.program with
    | .scalarU32,.scalar program => pure program
    | policy,.calls calls => do
      unless policy == .scalarU32CallsV1 || policy == .scalarU32ConstArgsV1 do throw "CTFE source policy/program mismatch"
      unless source.definition.crateIndex == 0 && calls.definition == source.definition.index do
        throw "calls policy requires exact local crate0 physical source identity"
      unless source.requiredConstants.isEmpty do throw "calls preamble must reside in the typed calls payload"
      unless source.promoted.isNone do throw "calls policy promoted sources unsupported"
      if policy == .scalarU32CallsV1 then
        unless calls.constantParameters.isEmpty && calls.typeParameters == source.parameters.size && source.parameters.all (· == .type) do
          throw "calls generic domain mismatch"
      else
        unless calls.typeParameters == 0 && !calls.constantParameters.isEmpty && source.parameters.all (· == .constant) &&
            calls.constantParameters.size == source.parameters.size do throw "const-args generic domain mismatch"
        for (parameter,index) in calls.constantParameters.zipIdx do
          unless parameter.index == index && parameter.ty == .uint 32 do throw "const-args declaration index/type mismatch"
      SourceStack.validateSource calls
      let program := calls.program
      unless source.localSources.size == program.locals.size && source.localMutability.size == program.locals.size do
        throw "CTFE calls local source-info domain mismatch"
      unless source.statementSources.size == program.blocks.size && source.terminatorSources.size == program.blocks.size do
        throw "CTFE calls block source-info domain mismatch"
      let info (value : SourceInfo) : Except String Unit :=
        unless value.scope < source.scopes.size do throw "CTFE calls source scope is absent"
      for value in source.localSources do info value
      for (scope,index) in source.scopes.zipIdx do
        if let some parent := scope.parent then
          unless parent < index do throw "CTFE calls scope parent is not earlier"
      for (block,index) in program.blocks.zipIdx do
        let some statements := source.statementSources[index]? | throw "CTFE calls source block absent"
        unless statements.size == block.statements.size do throw "CTFE calls statement source-info domain mismatch"
        for value in statements do info value
      for value in source.terminatorSources do info value
      return ()
    | _,_ => throw "CTFE source policy/program mismatch"
  unless source.requiredConstants.isEmpty do throw "scalar frame policy requires a separately evaluated required-constant preamble"
  unless program.argumentCount < program.locals.size do throw "CTFE source local/argument count mismatch"
  unless !program.blocks.isEmpty do throw "CTFE source has no blocks"
  unless source.localSources.size == program.locals.size && source.localMutability.size == program.locals.size do throw "CTFE local source-info domain mismatch"
  unless source.statementSources.size == program.blocks.size && source.terminatorSources.size == program.blocks.size do
    throw "CTFE block source-info domain mismatch"
  let info (value : SourceInfo) : Except String Unit :=
    unless value.scope < source.scopes.size do throw "CTFE source scope is absent"
  for value in source.localSources do info value
  for (scope,index) in source.scopes.zipIdx do
    if let some parent := scope.parent then
      unless parent < index do throw "CTFE scope parent is not an earlier source scope"
  let rec ty : Nat → ScalarFrame.Ty → Except String Unit
    | 0,_ => throw "CTFE source type traversal exhausted"
    | _,.uint bits => unless bits == 32 do throw "scalar CTFE source policy only covers u32"
    | _,.boolean | _,.unit | _,.never => pure ()
    | fuel+1,.pair a b => ty fuel a *> ty fuel b
  for value in program.locals do ty 16384 value
  let placeType (value : ScalarFrame.Place) : Except String ScalarFrame.Ty := do
    unless value.slot < program.locals.size do throw "CTFE source place local is absent"
    let some initialShape := program.locals[value.slot]? | throw "CTFE source place local is absent"
    let mut shape := initialShape
    for field in value.fields do
      match shape,field with
      | .pair a _,0 => shape := a
      | .pair _ b,1 => shape := b
      | _,_ => throw "CTFE source projection is outside its declared scalar type"
    pure shape
  let operandType (value : ScalarFrame.Operand) : Except String ScalarFrame.Ty :=
    match value with
    | .copy value | .move value => placeType value
    | .sourceValue source => pure source.value.ty
  let operand (value : ScalarFrame.Operand) : Except String Unit := do
    match value with
    | .copy value | .move value =>
      unless (← placeType value) != .never do throw "scalar CTFE source cannot read an uninhabited local"
    | .sourceValue source =>
      unless source.userType.isNone do throw "scalar CTFE source user-type annotation requires a complete source annotation domain"
      match source.value with
      | .uint bits value =>
        unless bits == 32 && value < 2^32 do throw "invalid raw CTFE u32 source literal"
      | .boolean _ | .unit => pure ()
      | _ => throw "raw CTFE source value contains a computed/unsupported value"
  let rvalueType (value : ScalarFrame.Rvalue) : Except String ScalarFrame.Ty := do
    match value with
    | .use value _ => operand value; operandType value
    | .binary kind left right =>
      operand left; operand right
      unless (← operandType left) == .uint 32 && (← operandType right) == .uint 32 do
        throw "scalar CTFE source binary operation requires u32 operands"
      pure (match kind with | .gt => .boolean | _ => .pair (.uint 32) .boolean)
  let target (value : Nat) : Except String Unit :=
    unless value < program.blocks.size do throw "CTFE source target block is absent"
  for (block,index) in program.blocks.zipIdx do
    let some statements := source.statementSources[index]? | throw "CTFE statement source-info domain mismatch"
    let some terminator := source.terminatorSources[index]? | throw "CTFE terminator source-info domain mismatch"
    unless statements.size == block.statements.size do
      throw "CTFE statement source-info domain mismatch"
    for value in statements do info value
    info terminator
    for statement in block.statements do
      match statement with
      | .live slot | .dead slot =>
        unless slot > 0 && slot < program.locals.size do throw "invalid CTFE source storage local"
      | .assign destination value =>
        let destinationType ← placeType destination
        unless destination.fields.isEmpty do throw "scalar CTFE source projected assignment is unsupported"
        unless destinationType == (← rvalueType value) do throw "CTFE source assignment contradicts declared local type"
      | .counter | .nop => pure ()
    match block.terminator with
    | .goto value => target value
    | .switch value cases otherwise =>
      operand value
      let shape ← operandType value
      unless shape == .uint 32 || shape == .boolean do throw "scalar CTFE switch type unsupported"
      let mut seen := #[]
      for (value,destination) in cases do
        unless value < (if shape == .boolean then 2 else 2^32) && !seen.contains value do
          throw "invalid or duplicate raw CTFE switch case"
        seen := seen.push value
        target destination
      target otherwise
    | .assert value _ (.overflow _ left right) destination =>
      operand value; operand left; operand right
      unless (← operandType value) == .boolean && (← operandType left) == .uint 32 &&
          (← operandType right) == .uint 32 do throw "scalar CTFE assertion operand type unsupported"
      target destination
    | .ret => pure ()

/-- Join raw source references against the current execution's source namespace,
without requesting layout, normalization, evaluation or allocation answers. -/
def validateReferences (spanCount : Nat) (knownDefinition : DefinitionIdentity → Bool)
    (source : Source) : Except String Unit := do
  validate source
  unless knownDefinition source.definition do throw "CTFE source physical definition is absent"
  let span (value : SpanRef) : Except String Unit :=
    unless value.id < spanCount do throw "CTFE source span reference is absent"
  span source.span
  for value in source.localSources do span value.span
  for values in source.statementSources do for value in values do span value.span
  for value in source.terminatorSources do span value.span
  for scope in source.scopes do
    span scope.span
    if let some root := scope.lintRoot then
      unless knownDefinition root.owner do throw "CTFE source lint owner is absent"
  let operand (value : ScalarFrame.Operand) : Except String Unit := do
    if let .sourceValue value := value then span ⟨value.span⟩
  if let .rawU64 program := source.program then
    span program.preambleDefSpan
    let rec term : Nat → GenericSubstitution.Term → Except String Unit
      | 0,_ => throw "raw u64 reference term traversal exhausted"
      | fuel+1,value => do
        match value with
        | .definition _ _ identity children =>
          unless knownDefinition identity do throw "raw u64 argument definition absent"
          let rec visit : GenericSubstitution.Terms → Except String Unit
            | .nil => pure ()
            | .cons child rest => term fuel child *> visit rest
          visit children
        | .node _ _ _ children =>
          let rec visitNode : GenericSubstitution.Terms → Except String Unit
            | .nil => pure ()
            | .cons child rest => term fuel child *> visitNode rest
          visitNode children
        | .binder _ body => term fuel body
        | _ => pure ()
    let reference (value : RawU64Frame.Reference) : Except String Unit := do
      unless knownDefinition value.definition do throw "raw u64 physical constant definition absent"
      span value.span
      for argument in value.arguments do term 16384 argument
    let operand : RawU64Frame.Operand → Except String Unit
      | .constant value => reference value
      | .sourceValue value => span value.span
      | _ => pure ()
    for value in program.required do reference value
    for statement in program.statements do
      match statement with
      | .assign _ (.use value _) | .assign _ (.unaryNot value) => operand value
      | _ => pure ()
    return ()
  let .scalar program := source.program | do
    let .calls calls := source.program | throw "CTFE program payload absent"
    let definition (index : Nat) : Except String Unit :=
      unless knownDefinition ⟨0,index⟩ do throw "CTFE local source reference is absent"
    let reference (value : CallFrame.Reference) : Except String Unit :=
      match value with
      | .parameterConstant _ _ _ location => span ⟨location⟩
      | .direct index _ _ location | .associated index _ _ _ location => definition index *> span ⟨location⟩
    let operand (value : CallFrame.Operand) : Except String Unit :=
      match value with
      | .constant value => reference value
      | .sourceValue value => span ⟨value.span⟩
      | _ => pure ()
    for value in calls.required do reference value
    for block in calls.program.blocks do
      for statement in block.statements do
        match statement with
        | .assign _ (.use value _) => operand value
        | .assign _ (.binary _ left right) => operand left *> operand right
        | _ => pure ()
      match block.terminator with
      | .call call =>
        definition call.callee
        span ⟨call.functionSpan⟩
        span ⟨call.functionOperandSpan⟩
        for value in call.argumentSpans do span ⟨value⟩
        for value in call.typeArguments do definition value
        for value in call.arguments do operand value
      | .switch value _ _ => operand value
      | .assert value _ message _ =>
        operand value
        match message with
        | .overflow _ left right => operand left *> operand right
        | .divisionByZero value => operand value
      | _ => pure ()
    return ()
  for block in program.blocks do
    for statement in block.statements do
      match statement with
      | .assign _ (.use value _) => operand value
      | .assign _ (.binary _ left right) => operand left *> operand right
      | _ => pure ()
    match block.terminator with
    | .switch value _ _ => operand value
    | .assert value _ (.overflow _ left right) _ => operand value *> operand left *> operand right
    | _ => pure ()

/-- Pinned best_lint_scope scans physical frames from root toward the active
callee. The returned source owner is input to an actual lint-level callback;
this function does not store or synthesize a lint answer. -/
def bestLintRoot (frames : List (Source × Nat × Nat)) : Except String (Option LintRoot) := do
  for (source,block,statement) in frames.reverse do
    let some sources := source.statementSources[block]? | throw "lint source block absent"
    let location ← if let some location := sources[statement]? then pure location else do
      unless statement == sources.size do throw "lint statement position absent"
      let some location := source.terminatorSources[block]? | throw "lint terminator source absent"
      pure location
    let rec find : Nat → Nat → Except String (Option LintRoot)
      | 0,_ => throw "lint scope traversal exhausted"
      | fuel+1,index => do
        let some scope := source.scopes[index]? | throw "lint scope absent"
        if let some root := scope.lintRoot then return some root
        if let some parent := scope.parent then find fuel parent else pure none
    if let some root ← find (source.scopes.size+1) location.scope then return some root
  pure none

def validateCatalogue (spanCount : Nat) (knownDefinition : DefinitionIdentity → Bool)
    (sources : Array Source) : Except String Unit := do
  let mut seen : Array (DefinitionIdentity × Option Nat × CompilerBodyRole) := #[]
  for source in sources do
    validateReferences spanCount knownDefinition source
    let key := (source.definition,source.promoted,source.role)
    unless !seen.contains key do throw "duplicate canonical CTFE source key"
    seen := seen.push key

/-- A missing source is Unsupported; equality of display paths never selects it. -/
def lookup (sources : Array Source) (definition : DefinitionIdentity) (promoted : Option Nat) :
    Except String Source := do
  let selected := sources.filter (fun source => source.definition == definition && source.promoted == promoted)
  let #[source] := selected | throw "CTFE source is absent or physically ambiguous"
  validate source
  pure source
end Miri.Input.CtfeMirSource
