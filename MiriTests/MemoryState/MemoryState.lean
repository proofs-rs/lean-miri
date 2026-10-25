import Miri.Memory.MemoryState

open Miri.ABI Miri.Memory

private structure TestHooks where
  events : Array String := #[]
  failInit : Bool := false
  failRoot : Bool := false
  failDealloc : Bool := false
  failCopy : Bool := false

private def event (state : TestHooks) (name : String) : TestHooks :=
  { state with events := state.events.push name }

private def hookResult (state : TestHooks) (value : α) : MachineHookResult TestHooks α :=
  ⟨state, .ok value⟩

private def hookFailure (state : TestHooks) (name : String) : MachineHookResult TestHooks α :=
  ⟨state, .error name⟩

private def allocationHookResult (memory : MemoryState Provenance Unit Unit)
    (state : TestHooks) (outcome : Except String α) :
    MemoryStateHookResult Provenance Unit Unit TestHooks α := ⟨memory,state,outcome⟩

private def testHooks : MemoryLifecycleHooks Provenance Unit Unit TestHooks Unit := {
  synchronizeMemory := fun _ state => state
  initLocalAllocation := fun memory state _ _ _ _ =>
    if state.failInit then allocationHookResult memory (event state "init-fail") (.error "init failed")
    else allocationHookResult memory (event state "init") (.ok ())
  adjustRootPointer := fun memory state id _ =>
    if state.failRoot then allocationHookResult memory (event state "root-fail") (.error "root failed")
    else allocationHookResult memory (event state "root") (.ok (Pointer.new (.concrete id BorTag.one) Size.ZERO))
  resolvePointer := fun memory state pointer _ =>
    let state := event state "resolve"
    match pointer.provenance with
    | some (.concrete id _) => ⟨memory,state, .ok (id, pointer.offset, ())⟩
    | _ => ⟨memory,state, .error pointer.offset.bytes⟩
  beforeDeallocation := fun memory state _ _ _ _ _ _ _ =>
    if state.failDealloc then allocationHookResult memory (event state "before-fail") (.error "deallocation hook failed")
    else allocationHookResult memory (event state "before") (.ok ())
  copyMemory := fun state memory source dest size _sameAllocation nonoverlapping => Id.run do
    let state := event state (if state.failCopy then "copy-fail" else "copy")
    if state.failCopy then
      return ⟨memory, state, .error "mem_copy failed"⟩
    let some (.concrete sourceId _) := source.provenance
      | return ⟨memory, state, .error "source pointer is not concrete"⟩
    let some (.concrete destId _) := dest.provenance
      | return ⟨memory, state, .error "destination pointer is not concrete"⟩
    let copied := MemoryLifecycle.copyResolvedRanges memory state sourceId source.offset
      destId dest.offset size 1 (Size.ofBytes 8) nonoverlapping
    return ⟨copied.memory, copied.hooks, copied.outcome.mapError toString⟩
}

private def smallSize : Size := Size.ofBytes 4
private def align : Align := Align.ONE
private def memoryKind : MemoryKind Unit := .machine ()
private def zeroedStorage (size : Size) (_align : Align) : Option (Array UInt8) :=
  some (Array.replicate size.bytes.toNat 0)

private def allocate (memory : MemoryState Provenance Unit Unit) (hooks : TestHooks) :=
  MemoryLifecycle.allocatePtr memory hooks (fun _ state => state) smallSize align memoryKind .Zero
    (Size.ofBytes 32) none zeroedStorage testHooks.initLocalAllocation
    testHooks.adjustRootPointer

private def requireOk (result : Except MemoryLifecycleError α) : IO α := do
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

private def eventText (state : TestHooks) : String := String.intercalate "," state.events.toList

private def isError : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

def main : IO Unit := do
  let empty : MemoryState Provenance Unit Unit := MemoryState.empty
  let initialized := allocate empty {}
  let pointer ← requireOk initialized.outcome
  let id ← match pointer.provenance with
    | .concrete id _ => pure id
    | .wildcard => throw (IO.userError "root pointer was wildcard")
  IO.println s!"allocate {id.value} live={initialized.memory.live.size} dead={initialized.memory.dead.size} issued={initialized.memory.issuedIds.size} error=false events={eventText initialized.hooks}"

  let badRoot := allocate empty { failRoot := true }
  IO.println s!"root-failure live={badRoot.memory.live.size} dead={badRoot.memory.dead.size} issued={badRoot.memory.issuedIds.size} error={isError badRoot.outcome} events={eventText badRoot.hooks}"

  let failedInit := allocate empty { failInit := true }
  IO.println s!"init-failure live={failedInit.memory.live.size} dead={failedInit.memory.dead.size} issued={failedInit.memory.issuedIds.size} error={isError failedInit.outcome} events={eventText failedInit.hooks}"

  let oversized := MemoryLifecycle.allocatePtr empty {} (fun _ state => state) smallSize align memoryKind .Zero
      (Size.ofBytes 2) none zeroedStorage
      testHooks.initLocalAllocation testHooks.adjustRootPointer
  IO.println s!"oversized live={oversized.memory.live.size} dead={oversized.memory.dead.size} issued={oversized.memory.issuedIds.size} error={isError oversized.outcome} events={eventText oversized.hooks}"

  let globalKind := MemoryLifecycle.allocatePtr empty {} (fun _ state => state) smallSize align memoryKind .Zero
      (Size.ofBytes 32) (some memoryKind) zeroedStorage
      testHooks.initLocalAllocation testHooks.adjustRootPointer
  IO.println s!"global-kind-assert live={globalKind.memory.live.size} dead={globalKind.memory.dead.size} issued={globalKind.memory.issuedIds.size} error={isError globalKind.outcome} events={eventText globalKind.hooks}"

  let exhausted := MemoryLifecycle.allocatePtr empty {} (fun _ state => state) smallSize align memoryKind .Zero
      (Size.ofBytes 32) none (fun _ _ => none)
      testHooks.initLocalAllocation testHooks.adjustRootPointer
  IO.println s!"host-exhaustion live={exhausted.memory.live.size} dead={exhausted.memory.dead.size} issued={exhausted.memory.issuedIds.size} error={isError exhausted.outcome} events={eventText exhausted.hooks}"

  let wrongKind := MemoryLifecycle.deallocatePtr initialized.memory initialized.hooks
    pointer.withOptionalProvenance none .stack testHooks
  IO.println s!"kind-failure live={wrongKind.memory.live.size} dead={wrongKind.memory.dead.size} issued={wrongKind.memory.issuedIds.size} error={isError wrongKind.outcome} events={eventText wrongKind.hooks}"

  let wrongLayout := MemoryLifecycle.deallocatePtr initialized.memory initialized.hooks
    pointer.withOptionalProvenance (some (Size.ofBytes 8, align)) memoryKind testHooks
  IO.println s!"layout-failure live={wrongLayout.memory.live.size} dead={wrongLayout.memory.dead.size} issued={wrongLayout.memory.issuedIds.size} error={isError wrongLayout.outcome} events={eventText wrongLayout.hooks}"

  let hookFailureState := { initialized.hooks with failDealloc := true }
  let hookFailure := MemoryLifecycle.deallocatePtr initialized.memory hookFailureState
    pointer.withOptionalProvenance none memoryKind testHooks
  IO.println s!"dealloc-hook-failure live={hookFailure.memory.live.size} dead={hookFailure.memory.dead.size} issued={hookFailure.memory.issuedIds.size} error={isError hookFailure.outcome} events={eventText hookFailure.hooks}"

  let deallocated := MemoryLifecycle.deallocatePtr initialized.memory initialized.hooks
    pointer.withOptionalProvenance none memoryKind testHooks
  let _ ← requireOk deallocated.outcome
  IO.println s!"deallocated live={deallocated.memory.live.size} dead={deallocated.memory.dead.size} issued={deallocated.memory.issuedIds.size} error=false events={eventText deallocated.hooks}"

  let secondFree := MemoryLifecycle.deallocatePtr deallocated.memory deallocated.hooks
    pointer.withOptionalProvenance none memoryKind testHooks
  IO.println s!"double-free live={secondFree.memory.live.size} dead={secondFree.memory.dead.size} issued={secondFree.memory.issuedIds.size} error={isError secondFree.outcome} events={eventText secondFree.hooks}"

  let offsetPointer := Pointer.new pointer.provenance (Size.ofBytes 1)
  let nonBase := MemoryLifecycle.deallocatePtr initialized.memory initialized.hooks
    offsetPointer.withOptionalProvenance none memoryKind testHooks
  IO.println s!"non-base-free live={nonBase.memory.live.size} dead={nonBase.memory.dead.size} issued={nonBase.memory.issuedIds.size} error={isError nonBase.outcome} events={eventText nonBase.hooks}"

  let reallocHooks := { initialized.hooks with failCopy := true }
  let realloc := MemoryLifecycle.reallocatePtr initialized.memory reallocHooks
      pointer.withOptionalProvenance (some (smallSize, align)) (Size.ofBytes 8) align
      memoryKind .Zero (Size.ofBytes 32) none zeroedStorage testHooks
  IO.println s!"copy-failure live={realloc.memory.live.size} error={isError realloc.outcome} events={eventText realloc.hooks}"

  let reallocOk := MemoryLifecycle.reallocatePtr initialized.memory initialized.hooks
      pointer.withOptionalProvenance (some (smallSize, align)) (Size.ofBytes 8) align
      memoryKind .Zero (Size.ofBytes 32) none zeroedStorage testHooks
  let newPointer ← requireOk reallocOk.outcome
  let newId ← match newPointer.provenance with
    | .concrete id _ => pure id
    | .wildcard => throw (IO.userError "reallocation returned a wildcard pointer")
  let some newAllocation := reallocOk.memory.live.find? fun entry => entry.1 == newId
    | throw (IO.userError "reallocated allocation is absent")
  let copiedBytes ← requireOk (newAllocation.2.allocation.getBytesUnchecked
      (allocRange Size.ZERO smallSize) |>.mapError MemoryLifecycleError.allocation)
  IO.println s!"copy-success live={reallocOk.memory.live.size} dead={reallocOk.memory.dead.size} bytes={copiedBytes.size} events={eventText reallocOk.hooks}"

theorem empty_has_no_live_or_dead_allocations :
    (MemoryState.empty : MemoryState Provenance Unit Unit).live = #[] ∧
      (MemoryState.empty : MemoryState Provenance Unit Unit).dead = #[] := by
  exact ⟨rfl, rfl⟩
