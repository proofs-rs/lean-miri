import Miri.MIR.Syntax
import Miri.Input.GenericSubstitution

/-! Source templates for ordinary generic copy/aggregate MIR. These datatypes
are distinct from executable MIR.Body: template type slots cannot be used as
runtime type IDs. Unsupported source instructions are not represented here;
the producer must classify them as a different body-seed category.

Pinned instance.rs:974–994 substitutes args_for_mir_body before normalization.
The supplied resolver must normalize and intern instantiated type material.
The coroutine source subset retains deref/field/downcast projections, raw Val
scalar/ZST operands, ADT aggregates, state discriminants, resume assertions and
drop control flow. Constants requiring CTFE, other rvalues and inlined scopes
remain explicit residual categories. Ordinary source calls retain their separate
restricted direct-call admission. -/
namespace Miri.Input.MirTemplate
open Miri.MIR GenericSubstitution

structure TypeSlot where
  index : Nat
  deriving Repr, DecidableEq

/-- Raw projected source places keep field type slots separate from runtime IDs. -/
inductive Projection where
  | deref
  | field (index : Nat) (type : TypeSlot)
  | downcast (name : Option String) (variant : Nat)
  | index (localId : LocalId)
  | constantIndex (offset minLength : Nat) (fromEnd : Bool)
  | subslice (fromIndex toIndex : Nat) (fromEnd : Bool)
  deriving Repr, DecidableEq
structure SourcePlace where
  localId : LocalId
  projection : Array Projection
  deriving Repr, DecidableEq
inductive SourceOperand where
  | copy (place : SourcePlace)
  | move (place : SourcePlace)
  | scalar (type : TypeSlot) (span : SpanRef) (bits bytes : Nat)
  | zeroSized (type : TypeSlot) (span : SpanRef)
  /-- Runtime post-CleanupPostBorrowck breadcrumbs. The canonical annotation
  table is explicitly known empty; this index must not be dereferenced into it. -/
  | annotatedScalar (type : TypeSlot) (span : SpanRef) (bits bytes userType : Nat)
  | annotatedZeroSized (type : TypeSlot) (span : SpanRef) (userType : Nat)
  deriving Repr, DecidableEq
structure SourceCallArgument where
  span : SpanRef
  operand : SourceOperand
  deriving Repr, DecidableEq
inductive SourceRvalue where
  | cast (kind : CastKind) (operand : SourceOperand) (target : TypeSlot)
  | reference (borrow : BorrowKind) (place : SourcePlace)
  | rawPointer (kind : RawPtrKind) (place : SourcePlace)
  | use (operand : SourceOperand) (retag : WithRetag)
  | discriminant (place : SourcePlace)
  | adt (type : TypeSlot) (variant : Nat) (operands : Array SourceOperand)
  | tuple (operands : Array SourceOperand)
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
  | sourceAssign (destination : SourcePlace) (value : SourceRvalue)
  | setDiscriminant (place : SourcePlace) (variant : Nat)
  | sourcePlaceMention (place : SourcePlace)
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
  | sourceCall (functionType : TypeSlot) (constantSpan : SpanRef)
      (arguments : Array SourceCallArgument) (destination : SourcePlace)
      (target : Option BasicBlockId) (unwind : UnwindAction) (functionSpan : SpanRef)
  | sourceSwitch (discriminant : SourceOperand) (targets : SwitchTargets)
  | assertResume (condition : SourceOperand) (expected : Bool) (message : AssertKind)
      (target : BasicBlockId) (unwind : UnwindAction)
  | sourceDrop (place : SourcePlace) (target : BasicBlockId) (unwind : UnwindAction)
      (replace : Bool) (asyncDrop : Option BasicBlockId)
  | unwindResume
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

def SourcePlace.instantiate {m : Type → Type} [Monad m]
    (resolve : TypeSlot → m TyId) (place : SourcePlace) : m Miri.MIR.Place := do
  let projection ← place.projection.mapM fun value => match value with
    | .deref => pure ProjectionElem.Deref
    | .field index type => return .Field index (← resolve type)
    | .downcast name variant => pure (.Downcast name variant)
    | .index localId => pure (.Index localId)
    | .constantIndex offset minLength fromEnd => pure (.ConstantIndex offset minLength fromEnd)
    | .subslice first last fromEnd => pure (.Subslice first last fromEnd)
  pure ⟨place.localId,projection⟩
def SourceOperand.instantiate {m : Type → Type} [Monad m]
    (resolve : TypeSlot → m TyId) : SourceOperand → m Miri.MIR.Operand
  | .copy place => return .Copy (← place.instantiate resolve)
  | .move place => return .Move (← place.instantiate resolve)
  | .scalar type span bits bytes => return .Constant ⟨span,none,.Val (.Scalar (.Int bits bytes)) (← resolve type)⟩
  | .zeroSized type span => return .Constant ⟨span,none,.Val .ZeroSized (← resolve type)⟩
  | .annotatedScalar type span bits bytes userType => return .Constant ⟨span,some userType,.Val (.Scalar (.Int bits bytes)) (← resolve type)⟩
  | .annotatedZeroSized type span userType => return .Constant ⟨span,some userType,.Val .ZeroSized (← resolve type)⟩
private def instantiateSourceRvalue {m : Type → Type} [Monad m]
    (resolve : TypeSlot → m TyId) (resolveAdt : TyId → Nat → m AggregateKind) :
    SourceRvalue → m Miri.MIR.Rvalue
  | .cast kind value target => return .Cast kind (← value.instantiate resolve) (← resolve target)
  | .reference borrow place => return .Ref .Erased borrow (← place.instantiate resolve)
  | .rawPointer kind place => return .RawPtr kind (← place.instantiate resolve)
  | .use value retag => return .Use (← value.instantiate resolve) retag
  | .discriminant place => return .Discriminant (← place.instantiate resolve)
  | .adt type variant operands => do
    let kind ← resolveAdt (← resolve type) variant
    return .Aggregate kind (← operands.mapM (SourceOperand.instantiate resolve))
  | .tuple operands => return .Aggregate .Tuple (← operands.mapM (SourceOperand.instantiate resolve))

private def instantiateRvalue {m : Type → Type} [Monad m]
    (resolve : TypeSlot → m TyId) : Rvalue → m Miri.MIR.Rvalue
  | .use value retag => pure (.Use value.instantiate retag)
  | .tuple values => pure (.Aggregate .Tuple (values.map Operand.instantiate))
  | .array element values => return .Aggregate (.Array (← resolve element)) (values.map Operand.instantiate)

private def instantiateStatement {m : Type → Type} [Monad m]
    (resolve : TypeSlot → m TyId) (resolveAdt : TyId → Nat → m AggregateKind) (source : Statement) : m Miri.MIR.Statement := do
  let kind : Miri.MIR.StatementKind ← match source.kind with
    | .sourceAssign place value => pure (.Assign (← place.instantiate resolve) (← instantiateSourceRvalue resolve resolveAdt value))
    | .setDiscriminant place variant => pure (.SetDiscriminant (← place.instantiate resolve) variant)
    | .sourcePlaceMention place => pure (.PlaceMention (← place.instantiate resolve))
    | .assign destination value =>
      pure (Miri.MIR.StatementKind.Assign (localPlace destination) (← instantiateRvalue resolve value))
    | .storageLive localId => pure (.StorageLive localId)
    | .storageDead localId => pure (.StorageDead localId)
    | .placeMention localId => pure (.PlaceMention (localPlace localId))
    | .nop => pure .Nop
  pure ⟨source.source,kind⟩

private def instantiateTerminator {m : Type → Type} [Monad m]
    (resolve : TypeSlot → m TyId) (source : Terminator) : m Miri.MIR.Terminator := do
  let kind : Miri.MIR.TerminatorKind ← match source.kind with
    | .sourceCall functionType constantSpan arguments destination target unwind functionSpan => do
      let function := Miri.MIR.Operand.Constant ⟨constantSpan,none,.Val .ZeroSized (← resolve functionType)⟩
      let arguments ← arguments.mapM fun argument => do
        pure ({span := argument.span,operand := ← argument.operand.instantiate resolve} : SpannedOperand)
      pure (.Call function arguments (← destination.instantiate resolve) target unwind .Normal functionSpan)
    | .sourceSwitch value targets => pure (.SwitchInt (← value.instantiate resolve) targets)
    | .assertResume value expected message target unwind => pure (.Assert (← value.instantiate resolve) expected message target unwind)
    | .sourceDrop place target unwind replace asyncDrop => pure (.Drop (← place.instantiate resolve) target unwind replace asyncDrop)
    | .unwindResume => pure .UnwindResume
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
  let place (value : SourcePlace) : Except String Unit := do
    localId value.localId
    for projection in value.projection do
      match projection with
      | .field _ type => slot type
      | .index id => localId id
      | _ => pure ()
  let sourceOperand (value : SourceOperand) : Except String Unit := do
    match value with
    | .copy value | .move value => place value
    | .scalar type _ bits bytes =>
      slot type
      unless bytes > 0 && bytes ≤ 16 && bits < 2^(8*bytes) do throw "MIR source scalar bits/width invalid"
    | .zeroSized type _ => slot type
    | .annotatedScalar type _ bits bytes userType =>
      slot type
      unless body.phase == .Runtime .Optimized && userType < 2^32 do
        throw "annotated source operand has wrong phase or raw index domain"
      unless bytes > 0 && bytes ≤ 16 && bits < 2^(8*bytes) do throw "MIR source scalar bits/width invalid"
    | .annotatedZeroSized type _ userType =>
      slot type
      unless body.phase == .Runtime .Optimized && userType < 2^32 do
        throw "annotated source operand has wrong phase or raw index domain"
  let unwind (value : UnwindAction) : Except String Unit := do
    if let .Cleanup id := value then
      unless id < body.blocks.size do throw "MIR template unwind target is out of bounds"
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
      | .sourceAssign destination value =>
        place destination
        match value with
        | .cast _ value target => sourceOperand value; slot target
        | .reference _ value | .rawPointer _ value => place value
        | .use value _ => sourceOperand value
        | .discriminant value => place value
        | .adt type _ values => slot type; for value in values do sourceOperand value
        | .tuple values => for value in values do sourceOperand value
      | .setDiscriminant value _ | .sourcePlaceMention value => place value
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
    | .sourceCall functionType _ arguments destination returnTarget action _ =>
      slot functionType
      place destination
      for argument in arguments do sourceOperand argument.operand
      for id in returnTarget.toArray do target id
      unwind action
    | .sourceSwitch value targets =>
      sourceOperand value
      let mut seen : Array Nat := #[]
      for .Case value id in targets.cases do
        unless value < 2^128 && !seen.contains value do throw "MIR template switch value is invalid or duplicated"
        seen := seen.push value
        target id
      target targets.otherwise
    | .assertResume condition _ message id action =>
      sourceOperand condition
      match message with
      | .ResumedAfterReturn _ | .ResumedAfterPanic _ | .ResumedAfterDrop _ => pure ()
      | _ => throw "MIR source assertion is outside resume diagnostics"
      target id
      unwind action
    | .sourceDrop value id action _ asyncDrop =>
      place value
      target id
      unwind action
      for id in asyncDrop.toArray do target id
    | .unwindResume => pure ()
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
operation, so nonempty binders explicitly reject here. Empty binders carry no
variables to anonymize and are retained exactly for ordinary FnDef arguments. -/
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
no nonempty binders, so every surviving bound variable here is escaping. -/
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

private def liftPure {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (result : Except String α) : m α :=
  match result with | .ok value => pure value | .error message => throw message

/-- Resolve only when the body is requested. Missing slots, normalization and
interning failures propagate. No executable skeleton or global cache exists. -/
def instantiate {m : Type → Type} [Monad m] [MonadExceptOf String m]
    (template : Template) (fuel : Nat) (args : Array Term)
    (resolveType : Term → m TyId)
    (resolveAdt : TyId → Nat → m AggregateKind := fun _ _ => throw "MIR source ADT aggregate resolver absent") : m Miri.MIR.Body := do
  liftPure (validate template args)
  let resolve (slot : TypeSlot) : m TyId := do
    let some expression := template.types[slot.index]? | throw "MIR template type slot is absent"
    resolveType (← liftPure (GenericSubstitution.instantiate fuel args expression))
  let locals ← template.skeleton.locals.mapM resolve
  let blocks ← template.skeleton.blocks.mapM fun block => do
    pure ⟨← block.statements.mapM (instantiateStatement resolve resolveAdt),
      ← instantiateTerminator resolve block.terminator,block.cleanup⟩
  pure ⟨template.skeleton.phase,template.skeleton.argumentCount,
    template.skeleton.spreadArgument,locals,blocks⟩

end Miri.Input.MirTemplate
