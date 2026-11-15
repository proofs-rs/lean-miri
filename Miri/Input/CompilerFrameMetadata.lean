import Miri.Input.SourceCompilerFrame
import Miri.Input.CompilerCallPipeline
import Miri.Interpreter.FrameMetadataBindings

/-! Exact compiler crate identity/name, caller attributes and source scopes.
The configured user-relevant crate set is supplied explicitly by the machine. -/
namespace Miri.Input.CompilerFrameMetadata
open Lean Miri.Interpreter
structure Prepared where
  calls : CompilerCallPipeline.Prepared
  localCrate : Nat
  crates : Array (Nat × String)

def prepare (calls : CompilerCallPipeline.Prepared) : Except String Prepared := do
  let source := calls.calls.program.input.queries.frameMetadata
  let localId := source.localCrate
  let mut crates := #[]
  for (id, name) in source.crates do
    if crates.any (·.1 == id) then throw "duplicate compiler crate identity"
    crates := crates.push (id, name)
  unless crates.any (·.1 == localId) do throw "local compiler crate name absent"
  return ⟨calls, localId, crates⟩

private def lift (result : Except String A) : MachineHooks.M K User A :=
  match result with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler frame metadata: {error}")

private def definitionCrate (p : Prepared) (callee : CallInstance) : Except String Nat := do
  let id ← CompilerInstance.definitionOf p.calls.calls.program.input.instances callee
  let some definition := p.calls.calls.program.compilerTables.definitions[id]?
    | throw "frame full-instance definition absent from shared compiler table"
  return definition.crateIndex

def hooks (p : Prepared) (userRelevantCrates : Array Nat) : FrameMetadata.CompilerHooks K User := {
  requiresCallerLocation := fun callee => do
    match CompilerVirtualFacts.inlineAttribute p.calls.scopes callee with
    | some value => pure value
    | none => lift (CompilerRuntimeQueries.requiresCallerLocation p.calls.runtime callee)
  isLocalDefinition := fun callee => return (← lift (definitionCrate p callee)) == p.localCrate
  definitionCrate := fun callee => lift (definitionCrate p callee)
  userRelevantCrate := fun id => pure (userRelevantCrates.contains id)
  crateName := fun id => lift do
    let some (_,name) := p.crates.find? (·.1 == id) | throw "compiler crate name absent"
    return name
  sourceScope := fun identity _ body scope => do
    let actual ← lift do
      let some actual := p.calls.scopes.program.bundle.bodies[identity.index]?
        | throw "canonical frame body identity absent"
      return actual
    unless actual.body == body do throw (.invalidProgram "frame body identity/content mismatch")
    lift (CompilerScopes.sourceScope p.calls.scopes identity.index scope) }

/-- Current canonical scope data, including exact inline instance and span IDs. -/
def sourceScope (world : SourceCompilerWorld.World) (identity : BodyIdentity)
    (callee : CallInstance) (mir : MIR.Body) (index : Nat) :
    Except String VirtualCalls.CallerScope := do
  let body ← SourceCompilerFrame.body world callee identity mir
  let some scope := body.sourceScopes[index]? | throw "canonical source scope absent"
  match scope.inlined with
  | none => return ⟨none,scope.inlinedParent⟩
  | some inline =>
    let _ ← SourceCompilerWorld.node world inline.instanceId
    unless inline.callsiteSpanId < world.canonical.spans.size do throw "inline callsite span absent"
    return ⟨some (inline.instanceId,⟨inline.callsiteSpanId⟩),scope.inlinedParent⟩

def requiresCallerLocation (world : SourceCompilerWorld.World) (callee : CallInstance) : Except String Bool := do
  let node ← SourceCompilerWorld.node world callee
  if let some material := world.canonical.sourceMaterial then
    unless matchesItem node.instanceKind do throw "typed source caller-location instance kind unsupported"
    let some definition := world.canonical.definitions[node.instanceKind.defId]?
      | throw "caller-location source definition absent"
    let some abi := material.abi | throw "typed source function attributes absent"
    let functions := abi.functions.filter (·.definition == definition)
    unless functions.size == 1 do throw "typed source function attributes absent/ambiguous"
    let some function := functions[0]? | throw "typed source function attributes absent"
    return function.attributes.trackCaller
  let inline := world.canonical.bodies.flatMap fun body => body.sourceScopes.filterMap fun scope =>
    scope.inlined.bind fun row => if row.instanceId == callee then some row.requiresCallerLocation else none
  if let some first := inline[0]? then
    unless inline.all (· == first) do throw "conflicting inline caller-location attributes"
    return first
  let some row := world.canonical.queries.runtime.instances.find? (·.instanceId == callee)
    | throw "current full-instance caller-location attribute absent"
  return row.requiresCallerLocation
where
  matchesItem : CallInstanceKind → Bool
    | .Item _ => true
    | _ => false

/-- Every compiler leaf reads the current shared World, including bodies added
since preparation. Crate names and source attributes remain actual evidence. -/
def liveHooks (access : SourceCompilerWorld.Access (MachineHooks.State K User))
    (userRelevantCrates : Array Nat) : FrameMetadata.CompilerHooks K User := Id.run do
  let current : MachineHooks.M K User SourceCompilerWorld.World := do
    let some world := access.get (← get)
      | throw (.unsupported "compiler frame metadata: source compiler World unavailable")
    return world
  return {
    requiresCallerLocation := fun callee => do lift (requiresCallerLocation (← current) callee)
    isLocalDefinition := fun callee => do
      let world ← current
      return (← lift (SourceCompilerFrame.definitionCrate world callee)) == world.canonical.queries.frameMetadata.localCrate
    definitionCrate := fun callee => do lift (SourceCompilerFrame.definitionCrate (← current) callee)
    userRelevantCrate := fun id => pure (userRelevantCrates.contains id)
    crateName := fun id => do
      let world ← current
      lift do
        let some (_,name) := world.canonical.queries.frameMetadata.crates.find? (·.1 == id)
          | throw "compiler crate name absent"
        return name
    sourceScope := fun identity callee mir scope => do
      lift (sourceScope (← current) identity callee mir scope) }

end Miri.Input.CompilerFrameMetadata

namespace Miri.Input.CompilerFrameMetadata
open Miri.MIR Miri.Interpreter Miri.Memory
set_option autoImplicit false
variable {K U P : Type}
def resolvedRank (localCrate definitionCrate : Nat) (relevant : Array Nat) : UInt8 :=
  if definitionCrate == localCrate || relevant.contains definitionCrate then 255 else 1
 theorem userRelevance_resolved (p : Prepared) (relevant : Array Nat)
    (frame : Frame P LocalLayout Unit) (definition : DefinitionId) (definitionIndex : Nat)
    (inline : CompilerVirtualFacts.inlineAttribute p.calls.scopes frame.functionInstance = none ∨
      CompilerVirtualFacts.inlineAttribute p.calls.scopes frame.functionInstance = (some false))
    (track : CompilerRuntimeQueries.requiresCallerLocation p.calls.runtime frame.functionInstance = .ok false)
    (resolved : CompilerInstance.definitionOf p.calls.calls.program.input.instances frame.functionInstance = .ok definitionIndex)
    (found : p.calls.calls.program.compilerTables.definitions[definitionIndex]? = some definition) :
    (FrameMetadata.userRelevance (hooks p relevant) frame : MachineHooks.M K U UInt8) =
      pure (resolvedRank p.localCrate definition.crateIndex relevant) := by
  rcases inline with inline | inline <;> funext state
  all_goals simp [FrameMetadata.userRelevance, hooks, lift, definitionCrate, inline, track, resolved, found,
    resolvedRank, bind, EStateM.bind, pure, EStateM.pure, Except.pure, Except.bind]
  all_goals split <;> simp_all [bind, EStateM.bind, EStateM.pure]
  all_goals split <;> rfl

 theorem initFrame_resolved (p : Prepared) (relevant : Array Nat)
    (frame : Frame Provenance LocalLayout Unit) (definition : DefinitionId) (definitionIndex : Nat)
    (inline : CompilerVirtualFacts.inlineAttribute p.calls.scopes frame.functionInstance = none ∨
      CompilerVirtualFacts.inlineAttribute p.calls.scopes frame.functionInstance = (some false))
    (track : CompilerRuntimeQueries.requiresCallerLocation p.calls.runtime frame.functionInstance = .ok false)
    (resolved : CompilerInstance.definitionOf p.calls.calls.program.input.instances frame.functionInstance = .ok definitionIndex)
    (found : p.calls.calls.program.compilerTables.definitions[definitionIndex]? = some definition)
    (state : MachineHooks.State K U) :
    ∃ fresh,
      MachineHooks.initFrame (FrameMetadata.userRelevance (hooks p relevant)) frame state = .ok fresh state ∧
      fresh.extra.borrowTracker = state.machine.borrowTracker.map (fun _ => {}) ∧
      fresh.extra.dataRace = state.machine.dataRace.map (fun _ => {}) ∧
      fresh.extra.userRelevance = resolvedRank p.localCrate definition.crateIndex relevant ∧
      fresh.returnContinuation = frame.returnContinuation ∧ fresh.returnPlace = frame.returnPlace := by
  have exactQuery := userRelevance_resolved (K := K) (U := U) p relevant frame definition definitionIndex inline track resolved found
  unfold MachineHooks.initFrame
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  rw [exactQuery]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

 def resolvedFrame (frame : Frame Provenance LocalLayout Unit)
    (machine : MachineHooks.MachineState K U) (rank : UInt8) :
    Frame Provenance LocalLayout MachineHooks.FrameExtra := {
  body := frame.body
  bodyIdentity := frame.bodyIdentity
  functionInstance := frame.functionInstance
  extra := { borrowTracker := machine.borrowTracker.map (fun _ => {})
             catchUnwind := none
             userRelevance := rank
             dataRace := machine.dataRace.map (fun _ => {}) }
  returnContinuation := frame.returnContinuation
  returnPlace := frame.returnPlace
  localsIdentity := frame.localsIdentity
  locals := frame.locals
  vaList := frame.vaList
  trackCallerArg := frame.trackCallerArg
  location := frame.location }
/-- The live frame constructor at its actual World/state. Caller attributes
and crate identity are pure queries against that same canonical source. -/
theorem initFrame_live_at
    (access : SourceCompilerWorld.Access (MachineHooks.State K U)) (relevant : Array Nat)
    (frame : Frame Provenance LocalLayout Unit) (world : SourceCompilerWorld.World)
    (state : MachineHooks.State K U) (localCrate definitionCrate : Nat)
    (present : access.get state = some world)
    (caller : requiresCallerLocation world frame.functionInstance = .ok false)
    (crate : SourceCompilerFrame.definitionCrate world frame.functionInstance = .ok definitionCrate)
    (localAt : world.canonical.queries.frameMetadata.localCrate = localCrate) :
    MachineHooks.initFrame (FrameMetadata.userRelevance (liveHooks access relevant)) frame state =
      .ok (resolvedFrame frame state.machine (resolvedRank localCrate definitionCrate relevant)) state := by
  have rank : FrameMetadata.userRelevance (liveHooks access relevant) frame state =
      .ok (resolvedRank localCrate definitionCrate relevant) state := by
    simp [FrameMetadata.userRelevance, liveHooks, lift, Id.run, present, caller, crate, localAt,
      resolvedRank, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]
    split <;> simp_all [lift, get, getThe, MonadStateOf.get, EStateM.get,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    all_goals split <;> rfl
  unfold MachineHooks.initFrame
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  rw [rank]
  rfl

 theorem initFrame_explicit (p : Prepared) (relevant : Array Nat)
    (frame : Frame Provenance LocalLayout Unit) (definition : DefinitionId) (definitionIndex : Nat)
    (inline : CompilerVirtualFacts.inlineAttribute p.calls.scopes frame.functionInstance = none ∨
      CompilerVirtualFacts.inlineAttribute p.calls.scopes frame.functionInstance = (some false))
    (track : CompilerRuntimeQueries.requiresCallerLocation p.calls.runtime frame.functionInstance = .ok false)
    (resolved : CompilerInstance.definitionOf p.calls.calls.program.input.instances frame.functionInstance = .ok definitionIndex)
    (found : p.calls.calls.program.compilerTables.definitions[definitionIndex]? = some definition)
    (state : MachineHooks.State K U) :
    MachineHooks.initFrame (FrameMetadata.userRelevance (hooks p relevant)) frame state =
      .ok (resolvedFrame frame state.machine (resolvedRank p.localCrate definition.crateIndex relevant)) state := by
  have exactQuery := userRelevance_resolved (K := K) (U := U) p relevant frame definition definitionIndex inline track resolved found
  unfold MachineHooks.initFrame
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  rw [exactQuery]
  rfl
end Miri.Input.CompilerFrameMetadata
open Lean Elab Command in
run_cmd do
  for name in #[``Miri.Input.CompilerFrameMetadata.initFrame_live_at,
      ``Miri.Input.CompilerFrameMetadata.userRelevance_resolved,
      ``Miri.Input.CompilerFrameMetadata.initFrame_resolved] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unexpected axiom: {name}: {dependency}"
