import Miri.MIR.Syntax
import Miri.Input.GenericSubstitution

/-! Source templates for ordinary generic copy/aggregate MIR. These datatypes
are distinct from executable MIR.Body: template type slots cannot be used as
runtime type IDs. Unsupported source instructions are not represented here;
the producer must classify them as a different body-seed category.

Pinned instance.rs:974–994 substitutes args_for_mir_body before normalization.
The supplied resolver must normalize and intern instantiated type material.
Constants requiring CTFE, calls, drops, projected places, inlined scopes and
coroutine bodies remain outside this initial template category. -/
namespace Miri.Input.MirTemplate
open Miri.MIR GenericSubstitution

structure TypeSlot where
  index : Nat
  deriving Repr, DecidableEq

inductive Operand where
  | copy (localId : LocalId)
  | move (localId : LocalId)
  deriving Repr, DecidableEq

inductive Rvalue where
  | use (operand : Operand) (retag : WithRetag)
  | tuple (operands : Array Operand)
  | array (element : TypeSlot) (operands : Array Operand)
  deriving Repr, DecidableEq

inductive StatementKind where
  | assign (destination : LocalId) (value : Rvalue)
  | storageLive (localId : LocalId)
  | storageDead (localId : LocalId)
  | placeMention (localId : LocalId)
  | nop
  deriving Repr, DecidableEq

structure Statement where
  source : SourceInfo
  kind : StatementKind
  deriving Repr, DecidableEq

structure CallArgument where
  span : SpanRef
  operand : Operand
  deriving Repr, DecidableEq

inductive TerminatorKind where
  | goto (target : BasicBlockId)
  | switchInt (discriminant : Operand) (targets : SwitchTargets)
  | call (functionType : TypeSlot) (constantSpan : SpanRef)
      (arguments : Array CallArgument) (destination : LocalId)
      (target : Option BasicBlockId) (unwind : UnwindAction)
      (callSource : CallSource) (functionSpan : SpanRef)
  | «return»
  | unreachable
  deriving Repr, DecidableEq

structure Terminator where
  source : SourceInfo
  kind : TerminatorKind
  deriving Repr, DecidableEq

structure Block where
  statements : Array Statement
  terminator : Terminator
  cleanup : Bool
  deriving Repr, DecidableEq

structure Skeleton where
  phase : MirPhase
  argumentCount : Nat
  spreadArgument : Option LocalId
  locals : Array TypeSlot
  blocks : Array Block
  deriving Repr, DecidableEq

structure Template where
  parameters : Array ArgSort
  types : Array Term
  skeleton : Skeleton
  deriving Repr

private def localPlace (localId : LocalId) : Miri.MIR.Place := ⟨localId,#[]⟩

def Operand.instantiate : Operand → Miri.MIR.Operand
  | .copy localId => .Copy (localPlace localId)
  | .move localId => .Move (localPlace localId)

private def instantiateRvalue (resolve : TypeSlot → Except String TyId) : Rvalue → Except String Miri.MIR.Rvalue
  | .use value retag => pure (.Use value.instantiate retag)
  | .tuple values => pure (.Aggregate .Tuple (values.map Operand.instantiate))
  | .array element values => return .Aggregate (.Array (← resolve element)) (values.map Operand.instantiate)

private def instantiateStatement (resolve : TypeSlot → Except String TyId) (source : Statement) :
    Except String Miri.MIR.Statement := do
  let kind : Miri.MIR.StatementKind ← match source.kind with
    | .assign destination value =>
      (instantiateRvalue resolve value).map (fun value => .Assign (localPlace destination) value)
    | .storageLive localId => pure (.StorageLive localId)
    | .storageDead localId => pure (.StorageDead localId)
    | .placeMention localId => pure (.PlaceMention (localPlace localId))
    | .nop => pure .Nop
  pure ⟨source.source,kind⟩

private def instantiateTerminator (resolve : TypeSlot → Except String TyId)
    (source : Terminator) : Except String Miri.MIR.Terminator := do
  let kind ← match source.kind with
    | .goto target => pure (.Goto target #[])
    | .switchInt value targets => pure (.SwitchInt value.instantiate targets)
    | .call functionType constantSpan arguments destination target unwind callSource functionSpan => do
      let function := Miri.MIR.Operand.Constant {
        span := constantSpan, userType := none, value := .Val .ZeroSized (← resolve functionType) }
      let arguments := arguments.map fun argument =>
        ({span := argument.span,operand := argument.operand.instantiate} : SpannedOperand)
      pure (.Call function arguments (localPlace destination) target unwind callSource functionSpan)
    | .return => pure .Return
    | .unreachable => pure .Unreachable
  pure ⟨source.source,kind⟩

private def validateParameters (parameters : Array ArgSort) : Nat → Term → Except String Unit
  | 0, _ => .error "MIR template parameter validation traversal exhausted"
  | fuel + 1, value => do
    match value with
    | .parameter sort index =>
      unless parameters[index]? == some sort do throw "MIR template parameter index/sort is invalid"
    | .binder _ value => validateParameters parameters fuel value
    | .node _ _ _ children | .definition _ _ _ children =>
      let _ ← children.mapM (fun child => do
        validateParameters parameters fuel child
        pure child)
      pure ()
    | _ => pure ()

def validateStructure (template : Template) : Except String Unit := do
  for sort in template.parameters do
    unless sort != .aggregate do throw "MIR template has an aggregate generic parameter"
  for ty in template.types do
    unless ty.sort == .type do throw "MIR template type slot has wrong sort"
    validateParameters template.parameters 16384 ty
  let body := template.skeleton
  unless body.argumentCount < body.locals.size do throw "MIR template argument/local count mismatch"
  unless !body.blocks.isEmpty do throw "MIR template has no basic blocks"
  let localId (id : Nat) : Except String Unit :=
    unless id < body.locals.size do throw "MIR template local is out of bounds"
  let slot (value : TypeSlot) : Except String Unit :=
    unless value.index < template.types.size do throw "MIR template type slot is absent"
  let operand (value : Operand) : Except String Unit :=
    match value with | .copy id | .move id => localId id
  let target (id : Nat) : Except String Unit :=
    unless id < body.blocks.size do throw "MIR template block target is out of bounds"
  for value in body.locals do slot value
  if let some spread := body.spreadArgument then
    unless spread > 0 && spread ≤ body.argumentCount do throw "MIR template has invalid spread argument"
  for block in body.blocks do
    for statement in block.statements do
      match statement.kind with
      | .assign destination value =>
        localId destination
        match value with
        | .use value _ => operand value
        | .tuple values => for value in values do operand value
        | .array element values =>
          slot element
          for value in values do operand value
      | .storageLive id | .storageDead id | .placeMention id => localId id
      | .nop => pure ()
    match block.terminator.kind with
    | .goto id => target id
    | .switchInt value targets =>
      operand value
      let mut seen : Array Nat := #[]
      for .Case value id in targets.cases do
        unless value < 2^128 && !seen.contains value do throw "MIR template switch value is invalid or duplicated"
        seen := seen.push value
        target id
      target targets.otherwise
    | .call functionType _ arguments destination returnTarget unwind _ _ =>
      slot functionType
      localId destination
      for argument in arguments do operand argument.operand
      for id in returnTarget.toArray do target id
      if let .Cleanup id := unwind then target id
    | .return | .unreachable => pure ()

def validate (template : Template) (args : Array Term) : Except String Unit := do
  validateStructure template
  unless args.size == template.parameters.size do throw "MIR template generic argument count mismatch"
  for (arg, expected) in args.zip template.parameters do
    unless arg.sort == expected do throw "MIR template generic argument sort mismatch"

/-- Free-region erasure for the binder-free constructor families admitted by
copy-template classification. Pinned erase_regions.rs:65–74 retains bound
regions and erases all others. Binder anonymization is a separate required
operation, so binder-bearing type families explicitly reject here. -/
def eraseFreeRegions : Nat → Term → Except String Term
  | 0, _ => .error "MIR template region-erasure traversal exhausted"
  | fuel + 1, value => do
    match value with
    | .binder variables inner =>
      unless variables.isEmpty do throw "MIR template normalization excludes nonempty binders"
      return .binder variables (← eraseFreeRegions fuel inner)
    | .bound .region .. => pure value
    | _ =>
      if value.sort == .region then return .atom .region "erased" ""
      match value with
      | .node sort tag payload children =>
        return .node sort tag payload (← children.mapM (eraseFreeRegions fuel))
      | .definition sort tag definition children =>
        return .definition sort tag definition (← children.mapM (eraseFreeRegions fuel))
      | _ => pure value

/-- The source exporter checks that instantiated MIR retains no parameters,
escaping bounds, inference variables or placeholders. The selected family has
no binders, so every surviving bound variable here is escaping. -/
def validateClosed : Nat → Term → Except String Unit
  | 0, _ => .error "MIR instantiated-type validation traversal exhausted"
  | fuel + 1, value => do
    match value with
    | .parameter .. | .bound .. | .placeholder .. | .inference .. =>
      throw "instantiated MIR retains unresolved generic variables"
    | .binder variables inner =>
      unless variables.isEmpty do throw "MIR template normalization excludes nonempty binders"
      validateClosed fuel inner
    | .node _ _ _ children | .definition _ _ _ children =>
      let _ ← children.mapM (fun child => do
        validateClosed fuel child
        pure child)
      pure ()
    | .atom .. => pure ()

/-- Resolve only when the body is requested. Missing slots, normalization and
interning failures propagate. No executable skeleton or global cache exists. -/
def instantiate (template : Template) (fuel : Nat) (args : Array Term)
    (resolveType : Term → Except String TyId) : Except String Miri.MIR.Body := do
  validate template args
  let resolve (slot : TypeSlot) : Except String TyId := do
    let some expression := template.types[slot.index]? | throw "MIR template type slot is absent"
    resolveType (← GenericSubstitution.instantiate fuel args expression)
  let locals ← template.skeleton.locals.mapM resolve
  let blocks ← template.skeleton.blocks.mapM fun block => do
    pure ⟨← block.statements.mapM (instantiateStatement resolve),
      ← instantiateTerminator resolve block.terminator,block.cleanup⟩
  pure ⟨template.skeleton.phase,template.skeleton.argumentCount,
    template.skeleton.spreadArgument,locals,blocks⟩

end Miri.Input.MirTemplate
