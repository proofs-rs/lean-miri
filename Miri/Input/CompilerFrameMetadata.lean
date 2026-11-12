import Miri.Input.CompilerCallPipeline
import Miri.Interpreter.FrameMetadataBindings
import Miri.Input.RuntimeArrayQueries

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

def definitionIndex (types : RuntimeArrayQueries.Access (MachineHooks.State K U))
    (callee : CallInstance) : MachineHooks.M K U Nat := do
  lift (CompilerInstance.definitionOf (← RuntimeArrayQueries.compilerSnapshot types) callee)

private def definitionCrate (p : Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K U)) (callee : CallInstance) : MachineHooks.M K U Nat := do
  let id ← definitionIndex types callee
  lift do
    let some definition := p.calls.calls.program.compilerTables.definitions[id]?
      | throw "frame full-instance definition absent from shared compiler table"
    return definition.crateIndex

def hooks (p : Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K User)) (userRelevantCrates : Array Nat) : FrameMetadata.CompilerHooks K User := {
  requiresCallerLocation := fun callee => do
    match CompilerVirtualFacts.inlineAttribute p.calls.scopes callee with
    | some value => pure value
    | none => RuntimeArrayQueries.performCompiler types (CompilerRuntimeQueries.requiresCallerLocation p.calls.runtime callee)
  isLocalDefinition := fun callee => return (← definitionCrate p types callee) == p.localCrate
  definitionCrate := fun callee => definitionCrate p types callee
  userRelevantCrate := fun id => pure (userRelevantCrates.contains id)
  crateName := fun id => lift do
    let some (_,name) := p.crates.find? (·.1 == id) | throw "compiler crate name absent"
    return name
  sourceScope := fun identity _ body scope => do
    let actual ← RuntimeArrayQueries.perform types (p.calls.scopes.program.resolveBody identity.index)
    unless actual.body == body do throw (.invalidProgram "frame body identity/content mismatch")
    lift (CompilerScopes.sourceScope p.calls.scopes identity.index scope) }

end Miri.Input.CompilerFrameMetadata

namespace Miri.Input.CompilerFrameMetadata
open Miri.MIR Miri.Interpreter Miri.Memory
set_option autoImplicit false
variable {K U P : Type}
def resolvedRank (localCrate definitionCrate : Nat) (relevant : Array Nat) : UInt8 :=
  if definitionCrate == localCrate || relevant.contains definitionCrate then 255 else 1
 theorem userRelevance_resolved (p : Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K U)) (relevant : Array Nat)
    (frame : Frame P LocalLayout Unit) (definition : DefinitionId) (definitionIndex : Nat)
    (inline : CompilerVirtualFacts.inlineAttribute p.calls.scopes frame.functionInstance = none ∨
      CompilerVirtualFacts.inlineAttribute p.calls.scopes frame.functionInstance = (some false))
    (track : RuntimeArrayQueries.performCompiler types (CompilerRuntimeQueries.requiresCallerLocation p.calls.runtime frame.functionInstance) = pure false)
    (resolved : CompilerFrameMetadata.definitionIndex types frame.functionInstance = pure definitionIndex)
    (found : p.calls.calls.program.compilerTables.definitions[definitionIndex]? = some definition) :
    (FrameMetadata.userRelevance (hooks p types relevant) frame : MachineHooks.M K U UInt8) =
      pure (resolvedRank p.localCrate definition.crateIndex relevant) := by
  rcases inline with inline | inline <;> funext state
  all_goals simp [FrameMetadata.userRelevance, hooks, lift, definitionCrate, inline, track, resolved, found,
    resolvedRank, bind, EStateM.bind, pure, EStateM.pure, Except.pure, Except.bind]
  all_goals split <;> simp_all [bind, EStateM.bind, EStateM.pure]
  all_goals split <;> rfl

 theorem initFrame_resolved (p : Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K U)) (relevant : Array Nat)
    (frame : Frame Provenance LocalLayout Unit) (definition : DefinitionId) (definitionIndex : Nat)
    (inline : CompilerVirtualFacts.inlineAttribute p.calls.scopes frame.functionInstance = none ∨
      CompilerVirtualFacts.inlineAttribute p.calls.scopes frame.functionInstance = (some false))
    (track : RuntimeArrayQueries.performCompiler types (CompilerRuntimeQueries.requiresCallerLocation p.calls.runtime frame.functionInstance) = pure false)
    (resolved : CompilerFrameMetadata.definitionIndex types frame.functionInstance = pure definitionIndex)
    (found : p.calls.calls.program.compilerTables.definitions[definitionIndex]? = some definition)
    (state : MachineHooks.State K U) :
    ∃ fresh,
      MachineHooks.initFrame (FrameMetadata.userRelevance (hooks p types relevant)) frame state = .ok fresh state ∧
      fresh.extra.borrowTracker = state.machine.borrowTracker.map (fun _ => {}) ∧
      fresh.extra.dataRace = state.machine.dataRace.map (fun _ => {}) ∧
      fresh.extra.userRelevance = resolvedRank p.localCrate definition.crateIndex relevant ∧
      fresh.returnContinuation = frame.returnContinuation ∧ fresh.returnPlace = frame.returnPlace := by
  have exactQuery := userRelevance_resolved (K := K) (U := U) p types relevant frame definition definitionIndex inline track resolved found
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
 theorem initFrame_explicit (p : Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K U)) (relevant : Array Nat)
    (frame : Frame Provenance LocalLayout Unit) (definition : DefinitionId) (definitionIndex : Nat)
    (inline : CompilerVirtualFacts.inlineAttribute p.calls.scopes frame.functionInstance = none ∨
      CompilerVirtualFacts.inlineAttribute p.calls.scopes frame.functionInstance = (some false))
    (track : RuntimeArrayQueries.performCompiler types (CompilerRuntimeQueries.requiresCallerLocation p.calls.runtime frame.functionInstance) = pure false)
    (resolved : CompilerFrameMetadata.definitionIndex types frame.functionInstance = pure definitionIndex)
    (found : p.calls.calls.program.compilerTables.definitions[definitionIndex]? = some definition)
    (state : MachineHooks.State K U) :
    MachineHooks.initFrame (FrameMetadata.userRelevance (hooks p types relevant)) frame state =
      .ok (resolvedFrame frame state.machine (resolvedRank p.localCrate definition.crateIndex relevant)) state := by
  have exactQuery := userRelevance_resolved (K := K) (U := U) p types relevant frame definition definitionIndex inline track resolved found
  unfold MachineHooks.initFrame
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  rw [exactQuery]
  rfl
end Miri.Input.CompilerFrameMetadata
open Lean Elab Command in
run_cmd do
  for name in #[``Miri.Input.CompilerFrameMetadata.userRelevance_resolved,
      ``Miri.Input.CompilerFrameMetadata.initFrame_resolved] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unexpected axiom: {name}: {dependency}"
