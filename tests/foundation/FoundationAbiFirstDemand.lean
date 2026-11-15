import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerWorldAbi
open Lean Miri Miri.Input Miri.Frontend.Foundation
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected genuine source")
  let source ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= decode)
  let seeded ← IO.ofExcept (compilerEntrySeed source)
  let queries := {seeded.canonical.queries with instanceAbis := #[]}
  let canonical := {seeded.canonical with functionAbis := #[],queries}
  let world := {seeded with derivedInstanceAbis := #[],canonical}
  let access : SourceCompilerWorld.Access SourceCompilerWorld.World := ⟨some,fun _ next => next⟩
  let mut state := world
  for node in world.canonical.instances do
    match SourceCompilerWorld.demandInstanceAbi access node.id #[] state with
    | .error error _ => throw (IO.userError (reprStr error))
    | .ok abi updated =>
      unless (← IO.ofExcept (SourceCompilerWorld.node updated node.id)).kind == .identityOnly do
        throw (IO.userError "ABI demand promoted MIR")
      match SourceCompilerWorld.bodyId updated node.id with
      | .error _ => pure ()
      | .ok _ => throw (IO.userError "ABI demand manufactured executable MIR")
      let before := (updated.canonical.types.size,updated.canonical.layouts.size,updated.canonical.functionAbis.size,updated.derivedInstanceAbis.size)
      match SourceCompilerWorld.demandInstanceAbi access node.id #[] updated with
      | .ok _ same =>
        unless (same.canonical.types.size,same.canonical.layouts.size,same.canonical.functionAbis.size,same.derivedInstanceAbis.size) == before do
          throw (IO.userError "repeated ABI demand changed canonical handles/cache")
      | .error error _ => throw (IO.userError (reprStr error))
      IO.println s!"first-demand {node.id}: args={abi.args.size},can_unwind={abi.canUnwind}; ABI-only identity retained"
      state := updated
  IO.println s!"derived {state.derivedInstanceAbis.size} new exact ABI keys from typed source only"
