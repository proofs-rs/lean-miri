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
  let raw ← calls.calls.program.input.raw.getObjVal? "compiler_frame_metadata"
  let localId ← (← raw.getObjVal? "local_crate").getNat?
  let mut crates := #[]
  for entry in (← (← raw.getObjVal? "crates").getArr?) do
    let id ← (← entry.getObjVal? "crate").getNat?
    let name ← (← entry.getObjVal? "name").getStr?
    if crates.any (·.1 == id) then throw "duplicate compiler crate identity"
    crates := crates.push (id,name)
  unless crates.any (·.1 == localId) do throw "local compiler crate name absent"
  return ⟨calls,localId,crates⟩

private def lift (result : Except String A) : MachineHooks.M K User A :=
  match result with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler frame metadata: {error}")

private def definitionCrate (p : Prepared) (callee : CallInstance) : Except String Nat := do
  let some definition := p.calls.calls.program.compilerTables.definitions[callee.defId]?
    | throw "frame full-instance definition absent from shared compiler table"
  return definition.crateIndex

def hooks (p : Prepared) (userRelevantCrates : Array Nat) : FrameMetadata.CompilerHooks K User := {
  requiresCallerLocation := fun callee => do
    match ← lift (CompilerVirtualFacts.inlineAttribute p.calls.scopes callee) with
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

end Miri.Input.CompilerFrameMetadata
