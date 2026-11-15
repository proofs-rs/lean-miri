import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerBodies
import Miri.Input.SourceCompilerAllocationIdentity
import Miri.Input.SourceAllocationIdentityInstallation
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .ok _ => throw (IO.userError "invalid identity material accepted") | .error _ => pure ()
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine snapshot source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  let some source := initial.canonical.sourceMaterial | throw (IO.userError "typed source absent")
  let some identity := source.allocationIdentity | throw (IO.userError "genuine allocation snapshot absent")
  let some physical := source.physical | throw (IO.userError "typed physical source absent")
  let mut world := initial
  for node in initial.canonical.instances do
    let (updated,_) ← checked (Input.SourceCompilerBodies.demandLoadedBody world node.id)
    world := updated
  let selected := world.canonical.types.find? (fun node => match node.shape with | .closure .. => true | _ => false)
  let some concrete := selected.orElse (fun _ => world.canonical.types.find? (fun node => match node.shape with | .tuple elements => elements.isEmpty | _ => false))
    | throw (IO.userError "genuine concrete unit/closure absent")
  let predicates := match world.canonical.types.find? (fun node => match node.shape with | .dynamicTraitObject .. => true | _ => false) with
    | some {shape := .dynamicTraitObject predicates .., ..} => predicates
    | _ => #[] -- Pinned no-principal vtables require only drop/size/align.
  let target ← checked (Input.SourcePhysical.target world)
  let memory : Memory.MemoryState Unit Unit Unit ← checked
    (Input.SourceAllocationIdentityInstallation.install world.canonical.sourceMaterial #[] .empty)
  unless memory.sourceAllocIdNext == identity.frontier do throw (IO.userError "snapshot frontier not installed")
  unless memory.sourceInitialFunctionDedupEmpty == !(identity.dedup.any (fun row => Input.SourceAllocationIdentity.Key.kind row.key == Input.SourceAllocationIdentity.Kind.function)) do
    throw (IO.userError "initial function dedup absence capability differs from complete snapshot")
  if let some global := identity.globals[0]? then
    let (knownMemory,known) := Input.SourceCompilerAllocationIdentity.importKnown identity global.rawId memory
    let known ← checked known
    unless knownMemory.sourceAllocIdNext == memory.sourceAllocIdNext &&
        knownMemory.sourceAllocIdForRuntime? known == some global.rawId do
      throw (IO.userError "known raw import consumed source frontier or lost raw identity")
  let (memory,stack) := memory.reserveAllocId
  let stack ← checked (stack.mapError (fun error => reprStr error))
  unless memory.sourceAllocIdForRuntime? stack == some identity.frontier do
    throw (IO.userError "ordinary allocation did not share source frontier")
  let result := Input.SourceCompilerAllocationIdentity.demand world memory concrete.id predicates ⟨0,by decide⟩
    target.defaultAddressSpacePointerSpec.pointerAlign
  let id ← checked result.outcome
  let raw := result.memory.sourceAllocIdForRuntime? id
  unless raw.isSome do throw (IO.userError "vtable raw crosswalk absent")
  let repeated := Input.SourceCompilerAllocationIdentity.demand result.world result.memory concrete.id predicates ⟨0,by decide⟩
    target.defaultAddressSpacePointerSpec.pointerAlign
  unless (← checked repeated.outcome) == id && repeated.memory.sourceAllocIdNext == result.memory.sourceAllocIdNext &&
      repeated.memory.globals.size == result.memory.globals.size do throw (IO.userError "vtable hit changed identity/frontier/global count")
  let wrapped := {repeated.memory with sourceAllocIdNext := 0}
  let wrappedHit := Input.SourceCompilerAllocationIdentity.demand repeated.world wrapped concrete.id predicates ⟨0,by decide⟩
    target.defaultAddressSpacePointerSpec.pointerAlign
  unless (← checked wrappedHit.outcome) == id && wrappedHit.memory.sourceAllocIdNext == 0 &&
      !wrappedHit.memory.sourceAllocIdExhausted do throw (IO.userError "wrapped frontier incorrectly blocked a dedup hit")
  let wrappedMiss := Input.SourceCompilerAllocationIdentity.demand repeated.world wrapped concrete.id predicates ⟨31,by decide⟩
    target.defaultAddressSpacePointerSpec.pointerAlign
  rejects wrappedMiss.outcome
  unless wrappedMiss.memory.sourceAllocIdExhausted do throw (IO.userError "wrapped frontier miss did not preserve allocator exhaustion effect")
  let other := Input.SourceCompilerAllocationIdentity.demand repeated.world repeated.memory concrete.id predicates ⟨1,by decide⟩
    target.defaultAddressSpacePointerSpec.pointerAlign
  unless (← checked other.outcome) != id do throw (IO.userError "distinct vtable salts aliased")
  let unavailableCanonical := {world.canonical with sourceMaterial := some {source with allocationIdentity := none}}
  let unavailable := {world with canonical := unavailableCanonical}
  let missing := Input.SourceCompilerAllocationIdentity.demand unavailable memory concrete.id predicates ⟨0,by decide⟩
    target.defaultAddressSpacePointerSpec.pointerAlign
  rejects missing.outcome
  unless missing.memory.sourceAllocIdNext == memory.sourceAllocIdNext do
    throw (IO.userError "missing initial witness consumed a raw number")
  let unknownFunction : Input.SourceAllocationIdentity.Material := {
    frontier := 2,globals := #[⟨1,.function⟩],dedup := #[⟨1,0,.unavailable .function⟩] }
  let _ ← checked (unknownFunction.validate physical.types.size)
  let nonemptyFunctionMemory : Memory.MemoryState Unit Unit Unit ← checked
    (Input.SourceAllocationIdentityInstallation.install
      (some {source with allocationIdentity := some unknownFunction}) #[] .empty)
  unless !nonemptyFunctionMemory.sourceInitialFunctionDedupEmpty do
    throw (IO.userError "nonempty unknown function family acquired empty-family capability")
  rejects ({identity with frontier := 0}.validate physical.types.size)
  let duplicate : Input.SourceAllocationIdentity.Material := {
    frontier := 3
    globals := #[⟨1,.vtable⟩,⟨2,.vtable⟩]
    dedup := #[⟨1,0,.vtable 0 0⟩,⟨2,0,.vtable 0 0⟩] }
  rejects (duplicate.validate physical.types.size)
  if let some row := identity.dedup.find? (fun row => match row.key with | .vtable .. => true | _ => false) then
    rejects ({identity with dedup := identity.dedup.push row}.validate physical.types.size)
  IO.println "genuine initial identity state shares frontier with ordinary allocation; vtable hits stable and salts distinct"
