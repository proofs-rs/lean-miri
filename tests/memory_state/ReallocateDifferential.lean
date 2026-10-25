import Miri.Memory.MemoryState

open Miri.ABI Miri.Memory

private structure TraceHooks where
  events : Array String := #[]
  fail : String := ""
  resolveCount : Nat := 0

private def emit (state : TraceHooks) (name : String) : TraceHooks :=
  { state with events := state.events.push name }

private def mkHookResult (state : TraceHooks) (value : α) : MachineHookResult TraceHooks α :=
  ⟨state, .ok value⟩

private def failHook (state : TraceHooks) (message : String) : MachineHookResult TraceHooks α :=
  ⟨state, .error message⟩

private def allocationHook (memory : MemoryState Provenance Unit Unit) (state : TraceHooks)
    (outcome : Except String α) : MemoryStateHookResult Provenance Unit Unit TraceHooks α :=
  ⟨memory,state,outcome⟩

private def hooks : MemoryLifecycleHooks Provenance Unit Unit TraceHooks Unit := {
  synchronizeMemory := fun _ state => state
  initLocalAllocation := fun memory state _ _ _ _ =>
    if state.fail == "init" then allocationHook memory (emit state "init-fail") (.error "init")
    else allocationHook memory (emit state "init") (.ok ())
  adjustRootPointer := fun memory state id _ =>
    if state.fail == "root" then allocationHook memory (emit state "root-fail") (.error "root")
    else allocationHook memory (emit state "root")
      (.ok (Pointer.new (.concrete id BorTag.one) Size.ZERO))
  resolvePointer := fun memory state pointer _ =>
    let count := state.resolveCount + 1
    let state := emit { state with resolveCount := count } "resolve"
    if (count == 1 && state.fail == "resolve1") ||
        (count == 2 && state.fail == "resolve2") then
      ⟨memory,state, .error pointer.offset.bytes⟩
    else
      match pointer.provenance with
      | some (.concrete id _) => ⟨memory,state, .ok (id, pointer.offset, ())⟩
      | _ => ⟨memory,state, .error pointer.offset.bytes⟩
  beforeDeallocation := fun memory state _ _ _ _ _ _ _ =>
    if state.fail == "before" then allocationHook memory (emit state "before-fail") (.error "before")
    else allocationHook memory (emit state "before") (.ok ())
  copyMemory := fun state memory source dest size _sameAllocation nonoverlapping => Id.run do
    let state := emit state (if state.fail == "copy" then "copy-fail" else "copy")
    if state.fail == "copy" then return ⟨memory, state, .error "copy"⟩
    let some (.concrete sourceId _) := source.provenance
      | return ⟨memory, state, .error "unresolved source"⟩
    let some (.concrete destId _) := dest.provenance
      | return ⟨memory, state, .error "unresolved destination"⟩
    let transferred := MemoryLifecycle.copyResolvedRanges memory state sourceId source.offset
        destId dest.offset size 1 (Size.ofBytes 8) nonoverlapping
    return ⟨transferred.memory, transferred.hooks, transferred.outcome.mapError toString⟩
}

private def initialMemory (present : Bool) : IO (MemoryState Provenance Unit Unit) := do
  let some id := AllocId.ofUInt64 1
    | throw (IO.userError "invalid test allocation id")
  let allocation ← match Allocation.tryNew (Prov := Provenance) (Size.ofBytes 4)
      Align.ONE .Zero (fun size _ => some (Array.replicate size.bytes.toNat 0)) with
    | .ok allocation => pure allocation
    | .error error => throw (IO.userError (toString error))
  let entry : LocalAllocation Provenance Unit Unit :=
    ⟨.machine (), allocation⟩
  let issued := MemoryState.setIssuedIds
    (MemoryState.empty : MemoryState Provenance Unit Unit) #[id]
  let issued := {issued with nextAllocId := 2}
  return {issued with live := if present then #[(id, entry)] else #[]}

private def runCase (tag failStage : String) (offset : UInt64)
    (oldSize : Option UInt64) (present : Bool) : IO Unit := do
  let memory ← initialMemory present
  let some id := AllocId.ofUInt64 1
    | throw (IO.userError "invalid test pointer id")
  let pointer := Pointer.new (.concrete id BorTag.one) (Size.ofBytes offset)
  let oldLayout := oldSize.map fun size => (Size.ofBytes size, Align.ONE)
  let hookState : TraceHooks := { fail := failStage }
  let storage := fun size _ =>
    if failStage == "host" then none
    else some (Array.replicate size.bytes.toNat 0)
  let result := MemoryLifecycle.reallocatePtr memory hookState pointer.withOptionalProvenance
      oldLayout (Size.ofBytes 8) Align.ONE (.machine ()) .Zero (Size.ofBytes 32) none
      storage hooks
  let events := String.intercalate "," result.hooks.events.toList
  let failed := match result.outcome with | .error _ => true | .ok _ => false
  IO.println s!"R {tag} error={failed} live={result.memory.live.size} dead={result.memory.dead.size} events={events}"

def main : IO Unit := do
  runCase "success-layout" "" 0 (some 4) true
  runCase "success-looked-up" "" 0 none true
  runCase "non-base" "" 1 (some 4) true
  runCase "host-failure" "host" 0 (some 4) true
  runCase "init-failure" "init" 0 (some 4) true
  runCase "root-failure" "root" 0 (some 4) true
  runCase "copy-failure" "copy" 0 (some 4) true
  runCase "before-failure" "before" 0 (some 4) true
  runCase "old-size-failure" "oldsize" 0 none false
  runCase "resolve-failure" "resolve1" 0 (some 4) true
  runCase "dealloc-resolve-failure" "resolve2" 0 (some 4) true
  runCase "layout-failure" "" 0 (some 3) true
