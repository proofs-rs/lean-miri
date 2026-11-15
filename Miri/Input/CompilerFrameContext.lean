import Miri.Input.SourceCompilerFrame
import Miri.Input.CompilerProviders
import Miri.Interpreter.AllocationDriver

/-! Canonical stack.rs frame/local/instruction queries. The body index is the
identity key; body contents only check consistency. Local layouts consume the concrete executable body’s resolved types. -/
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
  unless body.body == frame.body do throw "canonical body/content mismatch"
  let loaded ← CallResolution.loadedBodyOfInstance p.lifecycle.calls.calls frame.functionInstance
  unless loaded.identity == frame.bodyIdentity do throw "full-instance/canonical body identity mismatch"
  pure body

/-- The body was checked when installed. Runtime lookup only checks the frame's
canonical identity and ownership; it does not lower or rediscover source MIR. -/
def worldBodyOfFrame (world : SourceCompilerWorld.World) (frame : ActualFrame) :
    Except String Body := do
  SourceCompilerFrame.body world frame.functionInstance frame.bodyIdentity frame.body

private def currentWorld (access : SourceCompilerWorld.Access (MachineHooks.State K User)) :
    MachineHooks.M K User SourceCompilerWorld.World := do
  let some world := access.get (← get)
    | throw (.unsupported "compiler frame query: source compiler World unavailable")
  return world

def currentBody (access : SourceCompilerWorld.Access (MachineHooks.State K User)) :
    MachineHooks.M K User Body := do
  let world ← currentWorld access
  lift (worldBodyOfFrame world (← MachineHooks.currentFrame))

/-- Local types already belong to the concrete executable body. -/
def localType (world : SourceCompilerWorld.World) (frame : ActualFrame)
    (id : MIR.LocalId) : Except String MIR.TyId := do
  let body ← worldBodyOfFrame world frame
  let some ty := body.mir.locals[id]? | throw "local is absent"
  pure ty

/-- Read the current type/layout rows while retaining the validated target. -/
def computeLocalLayout (p : CompilerProviders.Prepared)
    (access : SourceCompilerWorld.Access (MachineHooks.State K User)) (id : MIR.LocalId) :
    MachineHooks.M K User LocalLayout := do
  let world ← currentWorld access
  let ty ← lift (localType world (← MachineHooks.currentFrame) id)
  lift (({p.runtime with source := world.canonical}.lookup ty).mapError toString)

/-- Exact query boundary, including absent World or canonical row failures.
No frame/local query effects are hidden in a success premise. -/
theorem computeLocalLayout_result_at (p : CompilerProviders.Prepared)
    (access : SourceCompilerWorld.Access (MachineHooks.State K User)) (id : MIR.LocalId)
    (before : MachineHooks.State K User) (frame : ActualFrame)
    (active : before.stack.currentFrame? = some frame) :
    computeLocalLayout p access id before =
      match access.get before with
      | none => .error (.unsupported "compiler frame query: source compiler World unavailable") before
      | some world =>
        let result : Except String LocalLayout := do
          let ty ← localType world frame id
          ({p.runtime with source := world.canonical} : RuntimeMetadata).lookup ty |>.mapError toString
        match result with
        | .ok layout => .ok layout before
        | .error reason => .error (.unsupported s!"compiler frame query: {reason}") before := by
  cases present : access.get before with
  | none =>
    simp [computeLocalLayout, currentWorld, present, get, getThe, MonadStateOf.get,
      EStateM.get, bind, EStateM.bind, pure, EStateM.pure] <;> rfl
  | some world =>
    cases localTypeAt : localType world frame id with
    | error reason =>
      simp [computeLocalLayout, currentWorld, MachineHooks.currentFrame, lift,
        present, active, localTypeAt, get, getThe, MonadStateOf.get, EStateM.get,
        bind, EStateM.bind, pure, EStateM.pure, Except.bind] <;> rfl
    | ok ty =>
      cases lookup : ({p.runtime with source := world.canonical} : RuntimeMetadata).lookup ty <;>
        simp [computeLocalLayout, currentWorld, MachineHooks.currentFrame, lift,
          present, active, localTypeAt, lookup, Except.mapError, get, getThe,
          MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure, Except.bind] <;> rfl

/-- Pointwise local-layout law at an actual current frame and canonical World.
All hypotheses are source/state data; the query's effects are derived here. -/
theorem computeLocalLayout_at (p : CompilerProviders.Prepared)
    (access : SourceCompilerWorld.Access (MachineHooks.State K User)) (id : MIR.LocalId)
    (before : MachineHooks.State K User) (world : SourceCompilerWorld.World)
    (frame : ActualFrame) (ty : MIR.TyId) (layout : LocalLayout)
    (present : access.get before = some world)
    (active : before.stack.currentFrame? = some frame)
    (localTypeAt : localType world frame id = .ok ty)
    (lookup : ({p.runtime with source := world.canonical} : RuntimeMetadata).lookup ty = .ok layout) :
    computeLocalLayout p access id before = .ok layout before := by
  simp [computeLocalLayout, currentWorld, MachineHooks.currentFrame, lift,
    present, active, localTypeAt, lookup, Except.mapError, get, getThe, MonadStateOf.get, EStateM.get,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Complete source layout_of_local for the actual current frame: a cached
layout bypasses lookup; debug compatibility runs before cache mutation. -/
def layoutOfLocal (p : CompilerProviders.Prepared)
    (access : SourceCompilerWorld.Access (MachineHooks.State K User)) (debugAssertions : Bool)
    (compatible : LocalLayout → LocalLayout → Except StepError Bool)
    (id : MIR.LocalId) (known : Option LocalLayout) : MachineHooks.M K User LocalLayout := do
  let frame ← MachineHooks.currentFrame
  let slot ← match frame.getLocal id with
    | .ok slot => pure slot
    | .error error => throw (.stack error)
  if let some cached := slot.layout then return cached
  let layout ← match known with
    | none => computeLocalLayout p access id
    | some known => do
      if debugAssertions then
        let computed ← computeLocalLayout p access id
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
def localSpan (p : CompilerProviders.Prepared) (supplied : MIR.Body) (id : MIR.LocalId) :
    MachineHooks.M K User MIR.SpanRef := do
  let frame ← MachineHooks.currentFrame
  unless supplied == frame.body do throw (.invalidProgram "local span body differs from active frame")
  let body ← lift (bodyOfFrame p frame)
  let some decl := body.input.localSources[id]? | throw (.invalidProgram "local source span index is absent")
  if decl.spanId < p.program.bundle.spans.size then
    pure ⟨decl.spanId⟩
  else throw (.unsupported "exact local source span is absent from canonical span table")

/-- Source spans use the current canonical body and span pool. -/
def liveLocalSpan (access : SourceCompilerWorld.Access (MachineHooks.State K User))
    (supplied : MIR.Body) (id : MIR.LocalId) : MachineHooks.M K User MIR.SpanRef := do
  let world ← currentWorld access
  let frame ← MachineHooks.currentFrame
  unless supplied == frame.body do throw (.invalidProgram "local span body differs from active frame")
  let body ← lift (worldBodyOfFrame world frame)
  let some declaration := body.localSources[id]?
    | throw (.invalidProgram "local source span index is absent")
  unless declaration.spanId < world.canonical.spans.size do
    throw (.unsupported "exact local source span is absent from canonical span table")
  return ⟨declaration.spanId⟩

/-- The local declaration span is read from the body owned by the actual
current World/frame. Coordinates or saved diagnostic spans do not select it. -/
theorem liveLocalSpan_at (access : SourceCompilerWorld.Access (MachineHooks.State K User))
    (supplied : MIR.Body) (id : MIR.LocalId) (before : MachineHooks.State K User)
    (world : SourceCompilerWorld.World) (frame : ActualFrame) (actual : Body) (declaration : SourceInfo)
    (present : access.get before = some world)
    (active : before.stack.currentFrame? = some frame)
    (sameBody : supplied = frame.body)
    (owned : worldBodyOfFrame world frame = .ok actual)
    (localAt : actual.localSources[id]? = some declaration)
    (bounded : declaration.spanId < world.canonical.spans.size) :
    liveLocalSpan access supplied id before = .ok ⟨declaration.spanId⟩ before := by
  simp [liveLocalSpan, currentWorld, MachineHooks.currentFrame, lift,
    present, active, sameBody, owned, localAt, bounded,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure]

/-- Return the actual existing MIR node; no second executable instruction IR. -/
def instruction (access : SourceCompilerWorld.Access (MachineHooks.State K User)) :
    MachineHooks.M K User (Option (Sum MIR.Statement MIR.Terminator)) := do
  let frame ← MachineHooks.currentFrame
  let _ ← lift (worldBodyOfFrame (← currentWorld access) frame)
  match frame.location with
  | .unwinding _ => pure none
  | .mir location =>
    let some block := frame.body.basicBlocks[location.block]?
      | throw (.stack (.invalidLocation location))
    if let some statement := block.statements[location.statementIndex]? then return some (.inl statement)
    if location.statementIndex == block.statements.size then return some (.inr block.terminator)
    throw (.stack (.invalidLocation location))

def sourceInfo (access : SourceCompilerWorld.Access (MachineHooks.State K User)) : MachineHooks.M K User (Option MIR.SourceInfo) := do
  match ← instruction access with
  | none => pure none
  | some (.inl statement) => pure (some statement.sourceInfo)
  | some (.inr terminator) => pure (some terminator.sourceInfo)

def currentSpan (access : SourceCompilerWorld.Access (MachineHooks.State K User)) : MachineHooks.M K User MIR.SpanRef := do
  let frame ← MachineHooks.currentFrame
  let _ ← lift (worldBodyOfFrame (← currentWorld access) frame)
  match AllocationDriver.frameSpan frame with
  | .ok span => pure span
  | .error error => throw error

/-- Source InterpCx::cur_span retains the actual enclosing compiler span for
an empty stack. The caller supplies that source context; no dummy is invented. -/
def curSpan (access : SourceCompilerWorld.Access (MachineHooks.State K User)) (contextSpan : MIR.SpanRef) :
    MachineHooks.M K User MIR.SpanRef := do
  if (← get).stack.frames.isEmpty then return contextSpan
  currentSpan access

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

def compilerFromLeaves (p : CompilerProviders.Prepared)
    (access : SourceCompilerWorld.Access (MachineHooks.State K User)) (h : CompilerLeaves K User C) :
    PlaceMachine.CompilerHooks K User C :=
  {debugAssertions := h.debugAssertions
   layout := fun _ id => computeLocalLayout p access id
   localSpan := liveLocalSpan access
   validationInProgress := h.validationInProgress
   projection := h.projection
   deref := h.deref
   checkPlaceType := h.checkPlaceType
   memoryOffset := h.memoryOffset
   debugAbiCheck := h.debugAbiCheck
   enforceValidity := h.enforceValidity
   validate := h.validate
   willValidateMemory := h.willValidateMemory}

def compilerHooks (p : CompilerProviders.Prepared)
    (access : SourceCompilerWorld.Access (MachineHooks.State K User)) (base : PlaceMachine.CompilerHooks K User C) :
    PlaceMachine.CompilerHooks K User C :=
  {base with layout := fun _ id => computeLocalLayout p access id, localSpan := liveLocalSpan access}

/-- Only TLS resolution remains a capability of the rvalue leaf record. -/
def rvalueLeaves (_p : CompilerProviders.Prepared)
    (threadLocalPointer : C → MIR.DefId → MachineHooks.M K User (Pointer (Option Provenance))) :
    ExecutionLeaves.Rvalue (MachineHooks.State K User) C :=
  ⟨threadLocalPointer⟩

/-- Close canonical frame access and local compiler leaves in the same config.
The existing operational dictionaries retain physical/validation capabilities. -/
def executionHooks (p : CompilerProviders.Prepared)
    (access : SourceCompilerWorld.Access (MachineHooks.State K User))
    (base : ExecutionMachine.Config K User C Other Extern Host) :
    ExecutionMachine.Config K User C Other Extern Host :=
  {base with
    compiler := compilerHooks p access base.compiler}
end Miri.Input.CompilerFrameContext

namespace Miri.Input.CompilerFrameContext
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false
variable {K U : Type}
 theorem localSpan_known (p : CompilerProviders.Prepared) (body : LoadedBody) (actual : LoweredBody)
    (fnInstance : CallInstance) (decl : SourceInfo) (span : SpanRef)
    (row : p.program.bundle.bodies[body.identity.index]? = some actual)
    (contents : actual.body = body.body)
    (loader : CallResolution.loadedBodyOfInstance p.lifecycle.calls.calls fnInstance = .ok body)
    (declaration : actual.input.localSources[0]? = some decl)
    (indexed : decl.spanId = span.id)
    (bounded : span.id < p.program.bundle.spans.size)
    (frames : Array ActualFrame) (frame : ActualFrame) (machine : MachineHooks.MachineState K U)
    (identity : frame.bodyIdentity = body.identity) (function : frame.functionInstance = fnInstance)
    (frameBody : frame.body = body.body) :
    localSpan p body.body 0 (⟨⟨frames.push frame⟩,machine⟩ : MachineHooks.State K U) =
      .ok span ⟨⟨frames.push frame⟩,machine⟩ := by
  simp [localSpan,MachineHooks.currentFrame,Stack.currentFrame?,bodyOfFrame,lift,
    row,contents,loader,declaration,indexed,bounded,identity,function,frameBody,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,Except.bind,Except.pure]
end Miri.Input.CompilerFrameContext

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``Miri.Input.CompilerFrameContext.liveLocalSpan_at) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved current local span axiom {dependency}"
