import Miri.Input.CompilerBodyRole
import Miri.Input.CompilerTypingEnv
import Miri.Interpreter.CompileTime.ScalarFrame

/-! Raw CTFE scalar-frame source, distinct from runtime MIR and query answers.
The accepted policy retains primitive source types/values and source locations;
it does not authorize whole constant-query evaluation or compiler allocation. -/
namespace Miri.Input.CtfeMirSource
open GenericSubstitution Miri.MIR
open Miri.Interpreter.CompileTime
inductive Policy where
  | scalarU32
  deriving Repr, DecidableEq
structure LintRoot where
  owner : DefinitionIdentity
  localId : Nat
  deriving Repr
structure Scope where
  span : SpanRef
  parent : Option Nat
  lintRoot : Option LintRoot
  deriving Repr
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
  program : ScalarFrame.Program
  localSources : Array SourceInfo
  localMutability : Array Bool
  statementSources : Array (Array SourceInfo)
  terminatorSources : Array SourceInfo
  scopes : Array Scope
  deriving Repr

def validate (source : Source) : Except String Unit := do
  unless source.role == .ctfe do throw "CTFE source requires the CTFE compiler body role"
  unless source.phase == .Runtime .PostCleanup do throw "scalar CTFE source has wrong MIR acquisition phase"
  unless source.environment == .declaration source.definition .postAnalysis do
    throw "CTFE source declaration environment recipe contradicts its source owner/mode"
  unless source.parameters.all (· != .aggregate) do throw "invalid CTFE declaration parameter sort"
  unless source.requiredConstants.isEmpty do throw "scalar frame policy requires a separately evaluated required-constant preamble"
  let program := source.program
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
  for block in source.program.blocks do
    for statement in block.statements do
      match statement with
      | .assign _ (.use value _) => operand value
      | .assign _ (.binary _ left right) => operand left *> operand right
      | _ => pure ()
    match block.terminator with
    | .switch value _ _ => operand value
    | .assert value _ (.overflow _ left right) _ => operand value *> operand left *> operand right
    | _ => pure ()

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
