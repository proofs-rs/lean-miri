import Miri.Input.CompilerProviders
import Miri.Interpreter.AllocationDriver

/-! Canonical stack.rs frame/local/instruction queries. The body index is the
identity key; body contents only check consistency. Local layouts consume exact
full-instance body-normalization evidence, never template type substitution. -/
namespace Miri.Input.CompilerFrameContext
open Lean Miri.ABI Miri.Memory Miri.Interpreter
abbrev ActualFrame := Frame Provenance LocalLayout MachineHooks.FrameExtra
private def lift (query : Except String A) : MachineHooks.M K User A :=
  match query with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler frame query: {error}")

/-- Resolve by canonical identity and validate the complete instance/body pair.
Structural equality is an assertion, not a body-selection algorithm. -/
def bodyOfFrame (p : CompilerProviders.Prepared) (frame : ActualFrame) :
    Except String LoweredBody := do
  let some body := p.program.bundle.bodies[frame.bodyIdentity.index]?
    | throw "canonical body identity is absent"
  unless body.bodyId == frame.bodyId do throw "canonical body ID mismatch"
  unless body.body == frame.body do
    throw "canonical body metadata mismatch"
  let loaded ← CallResolution.loadedBodyOfInstance p.lifecycle.calls.calls frame.functionInstance
  unless loaded.identity == frame.bodyIdentity do throw "full-instance/canonical body identity mismatch"
  pure body

def currentBody (p : CompilerProviders.Prepared) : MachineHooks.M K User LoweredBody := do
  lift (bodyOfFrame p (← MachineHooks.currentFrame))

private def normalizedBodyAfterContext (p : CompilerProviders.Prepared) (frame : ActualFrame) :
    Except String MIR.BodyNode := do
  let some lifecycle := p.lifecycle.lifecycle.entries[frame.bodyIdentity.index]?
    | throw "canonical body compiler context is absent"
  unless (← lifecycle.callee) == frame.functionInstance do
    throw "body normalization belongs to another full instance"
  p.program.input.mirTables.normalizedBody frame.bodyIdentity.index

def normalizedBody (p : CompilerProviders.Prepared) (frame : ActualFrame) :
    Except String MIR.BodyNode := do
  let _ ← bodyOfFrame p frame
  normalizedBodyAfterContext p frame

def normalizedLocalType (p : CompilerProviders.Prepared) (frame : ActualFrame)
    (id : MIR.LocalId) : Except String MIR.TyId := do
  let body ← bodyOfFrame p frame
  let some source := body.input.locals[id]? | throw "source local is absent"
  unless source.id == id do throw "source local index mismatch"
  let normalized ← normalizedBodyAfterContext p frame
  unless normalized.locals.size == body.input.locals.size do throw "body normalization changed local count"
  let some ty := normalized.locals[id]? | throw "normalized local is absent"
  return ty

theorem normalizedLocalType_body (p : CompilerProviders.Prepared) (frame : ActualFrame)
    (id : MIR.LocalId) (ty : MIR.TyId) (body : LoweredBody)
    (row : p.program.bundle.bodies[frame.bodyIdentity.index]? = some body)
    (known : normalizedLocalType p frame id = .ok ty) :
    body.bodyId = frame.bodyId ∧ body.body = frame.body := by
  unfold normalizedLocalType at known
  cases selected : bodyOfFrame p frame with
  | error reason => simp [selected, bind, Except.bind] at known
  | ok actual =>
      unfold bodyOfFrame at selected
      simp only [row, bind, Except.bind] at selected
      by_cases wire : (body.bodyId == frame.bodyId) = true
      · by_cases contents : (body.body == frame.body) = true
        · exact ⟨beq_iff_eq.mp wire, beq_iff_eq.mp contents⟩
        · simp [wire, contents, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at selected
      · simp [wire, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at selected

theorem normalizedLocalType_congr (p : CompilerProviders.Prepared) (left right : ActualFrame)
    (id : MIR.LocalId) (body : left.body = right.body) (bodyId : left.bodyId = right.bodyId)
    (identity : left.bodyIdentity = right.bodyIdentity)
    (function : left.functionInstance = right.functionInstance) :
    normalizedLocalType p left id = normalizedLocalType p right id := by
  simp only [normalizedLocalType, normalizedBodyAfterContext, bodyOfFrame,
    body, bodyId, identity, function]

private def castTarget (tables : MIR.SyntaxTables) (body : MIR.BodyNode) (location : MIR.Location) : Except String MIR.TyId := do
  let some id := body.basicBlocks[location.block]? | throw "cast block is absent"
  let block ← tables.blocks.lookup id.index |>.mapError (fun _ => "cast block ID is invalid")
  let some id := block.statements[location.statementIndex]? | throw "cast statement is absent"
  let statement ← tables.statements.lookup id.index |>.mapError (fun _ => "cast statement ID is invalid")
  let .Assign _ id := statement.kind | throw "cast normalization outside an Assign"
  let value ← tables.rvalues.lookup id.index |>.mapError (fun _ => "cast rvalue ID is invalid")
  let .Cast _ _ target := value | throw "cast normalization outside a Cast"
  return target

def normalizeCastTarget (p : CompilerProviders.Prepared) (requested : MIR.TyId) :
    MachineHooks.M K User MIR.TyId := do
  let frame ← MachineHooks.currentFrame
  let .mir location := frame.location | throw .expectedMirLocation
  let tables := p.program.input.mirTables.mir
  let original ← lift (castTarget tables frame.body location)
  unless requested == original do throw (.invalidProgram "cast normalization requested another source type")
  lift do castTarget tables (← normalizedBody p frame) location

/-- The uncached compiler leaf used by the canonical local-layout cache. -/
def computeLocalLayout (p : CompilerProviders.Prepared) (id : MIR.LocalId) :
    MachineHooks.M K User LocalLayout := do
  let frame ← MachineHooks.currentFrame
  let ty ← lift (normalizedLocalType p frame id)
  lift ((p.runtime.lookup ty).mapError toString)

/-- Complete source layout_of_local for the actual current frame: a cached
layout bypasses normalization; debug compatibility runs before cache mutation. -/
def layoutOfLocal (p : CompilerProviders.Prepared) (debugAssertions : Bool)
    (compatible : LocalLayout → LocalLayout → Except StepError Bool)
    (id : MIR.LocalId) (known : Option LocalLayout) : MachineHooks.M K User LocalLayout := do
  let frame ← MachineHooks.currentFrame
  let slot ← match frame.getLocal id with
    | .ok slot => pure slot
    | .error error => throw (.stack error)
  if let some cached := slot.layout then return cached
  let layout ← match known with
    | none => computeLocalLayout p id
    | some known => do
      if debugAssertions then
        let computed ← computeLocalLayout p id
        let same ← match compatible computed known with
          | .ok same => pure same
          | .error error => throw error
        unless same do throw (.invalidProgram "known local layout differs from compiler layout")
      pure known
  let frame ← MachineHooks.currentFrame
  let (frame,layout) ← match frame.getOrCacheLocalLayout id layout with
    | .ok result => pure result
    | .error error => throw (.stack error)
  MachineHooks.setCurrentFrame frame
  pure layout

/-- The passed body is checked against the current identity, never searched. -/
def localSpan (p : CompilerProviders.Prepared) (supplied : BodyIdentity) (id : MIR.LocalId) :
    MachineHooks.M K User MIR.SpanRef := do
  let frame ← MachineHooks.currentFrame
  unless supplied == frame.bodyIdentity do throw (.invalidProgram "local span body differs from active frame")
  let body ← lift (bodyOfFrame p frame)
  let some decl := body.input.locals[id]? | throw (.invalidProgram "local source span index is absent")
  match p.program.bundle.spans.toList.idxOf? decl.sourceInfo.span with
  | some index => pure ⟨index⟩
  | none => throw (.unsupported "exact local source span is absent from canonical span table")

/-- Compiler queries use their owning input's table. A frame's independent
execution table is not evidence for a canonical compiler source query. -/
@[inline] def canonicalFrame (p : CompilerProviders.Prepared) (frame : ActualFrame) : ActualFrame :=
  {frame with mirTables := p.program.input.mirTables.mir}

/-- Return the actual existing MIR node; no second executable instruction IR. -/
def instruction (p : CompilerProviders.Prepared) :
    MachineHooks.M K User (Option (Sum MIR.StatementNode MIR.TerminatorNode)) := do
  let frame ← MachineHooks.currentFrame
  let _ ← lift (bodyOfFrame p frame)
  match (canonicalFrame p frame).instruction? with
  | .ok instruction => pure instruction
  | .error error => throw (.stack error)

def sourceInfo (p : CompilerProviders.Prepared) : MachineHooks.M K User (Option MIR.SourceInfo) := do
  match ← instruction p with
  | none => pure none
  | some (.inl statement) => pure (some statement.sourceInfo)
  | some (.inr terminator) => pure (some terminator.sourceInfo)

def currentSpan (p : CompilerProviders.Prepared) : MachineHooks.M K User MIR.SpanRef := do
  let frame ← MachineHooks.currentFrame
  let _ ← lift (bodyOfFrame p frame)
  match AllocationDriver.frameSpan (canonicalFrame p frame) with
  | .ok span => pure span
  | .error error => throw error

/-- Source InterpCx::cur_span retains the actual enclosing compiler span for
an empty stack. The caller supplies that source context; no dummy is invented. -/
def curSpan (p : CompilerProviders.Prepared) (contextSpan : MIR.SpanRef) :
    MachineHooks.M K User MIR.SpanRef := do
  if (← get).stack.frames.isEmpty then return contextSpan
  currentSpan p

/-- Remaining capabilities after source-owned local layout/span queries are
removed. These concern typed operations, validation and compiler predicates. -/
structure CompilerLeaves (K User C : Type) where
  debugAssertions : Bool
  validationInProgress : MachineHooks.M K User Bool
  projection : C → MachineHooks.M K User (ProjectionCx Provenance)
  deref : C → RuntimePlace Provenance → Bool → MachineHooks.M K User (RuntimePlace Provenance)
  checkPlaceType : C → MIR.Place → RuntimePlace Provenance → MachineHooks.M K User Unit
  memoryOffset : C → MemPlace Provenance → Size → OffsetMode → MemPlaceMeta Provenance → MachineHooks.M K User (MemPlace Provenance)
  debugAbiCheck : Immediate Provenance → LocalLayout → MachineHooks.M K User Unit
  enforceValidity : C → LocalLayout → MachineHooks.M K User Bool
  validate : C → RuntimePlace Provenance → MachineHooks.M K User Unit
  willValidateMemory : MemoryOperandLayout → Bool

def compilerFromLeaves (p : CompilerProviders.Prepared) (h : CompilerLeaves K User C) :
    PlaceMachine.CompilerHooks K User C :=
  {debugAssertions := h.debugAssertions
   layout := fun _ id => computeLocalLayout p id
   localSpan := localSpan p
   validationInProgress := h.validationInProgress
   projection := h.projection
   deref := h.deref
   checkPlaceType := h.checkPlaceType
   memoryOffset := h.memoryOffset
   debugAbiCheck := h.debugAbiCheck
   enforceValidity := h.enforceValidity
   validate := h.validate
   willValidateMemory := h.willValidateMemory}

def compilerHooks (p : CompilerProviders.Prepared) (base : PlaceMachine.CompilerHooks K User C) :
    PlaceMachine.CompilerHooks K User C :=
  {base with layout := fun _ id => computeLocalLayout p id, localSpan := localSpan p}

/-- Only TLS resolution remains a capability of the rvalue leaf record. -/
def rvalueLeaves (p : CompilerProviders.Prepared)
    (threadLocalPointer : C → MIR.DefId → MachineHooks.M K User (Pointer (Option Provenance))) :
    ExecutionLeaves.Rvalue (MachineHooks.State K User) C :=
  ⟨threadLocalPointer,fun _ ty => normalizeCastTarget p ty⟩

/-- Close canonical frame access and local compiler leaves in the same config.
The existing operational dictionaries retain physical/validation capabilities. -/
def executionHooks (p : CompilerProviders.Prepared)
    (base : ExecutionMachine.Config K User C Other Extern Host) :
    ExecutionMachine.Config K User C Other Extern Host :=
  {base with
    compiler := compilerHooks p base.compiler
    rvalues := {base.rvalues with normalize := fun _ ty => normalizeCastTarget p ty}}
end Miri.Input.CompilerFrameContext

namespace Miri.Input.CompilerFrameContext
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false
variable {K U : Type}
 theorem localSpan_known (p : CompilerProviders.Prepared) (body : LoadedBody) (actual : LoweredBody)
    (fnInstance : CallInstance) (decl : LocalDecl) (span : SpanRef)
    (row : p.program.bundle.bodies[body.identity.index]? = some actual)
    (contents : actual.body = body.body)
    (wire : actual.bodyId = body.bodyId)
    (loader : CallResolution.loadedBodyOfInstance p.lifecycle.calls.calls fnInstance = .ok body)
    (declaration : actual.input.locals[0]? = some decl)
    (indexed : p.program.bundle.spans.toList.idxOf? decl.sourceInfo.span = some span.id)
    (frames : Array ActualFrame) (frame : ActualFrame) (machine : MachineHooks.MachineState K U)
    (identity : frame.bodyIdentity = body.identity) (function : frame.functionInstance = fnInstance)
    (frameBody : frame.body = body.body) (frameId : frame.bodyId = body.bodyId) :
    localSpan p body.identity 0 (⟨⟨frames.push frame⟩,machine⟩ : MachineHooks.State K U) =
      .ok span ⟨⟨frames.push frame⟩,machine⟩ := by
  simp [localSpan,MachineHooks.currentFrame,Stack.currentFrame?,bodyOfFrame,lift,
    row,contents,wire,loader,declaration,indexed,identity,function,frameBody,frameId,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,Except.bind,Except.pure]
end Miri.Input.CompilerFrameContext
