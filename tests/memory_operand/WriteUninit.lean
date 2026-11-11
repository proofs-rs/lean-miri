import Miri.Interpreter.MemoryOperand

open Miri.ABI Miri.Memory Miri.Interpreter

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def sz (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)
private def runtime : RuntimeTargetDataLayout :=
  {RuntimeTargetDataLayout.default with base := ⟨.little, .w64⟩}

private def globals : GlobalAllocationHooks CtfeProvenance Unit Unit Nat := {
  synchronizeMemory := fun _ state => state
  evaluateStaticInitializer := fun memory state _ => ⟨memory, state, .error "unused"⟩
  beforeAccessGlobal := fun memory state _ _ _ _ => ⟨memory, state, .ok ()⟩
  adjustGlobalAllocation := fun memory state _ allocation => ⟨memory, state, .ok (.borrowed allocation)⟩ }

private def accesses (deny : Bool) : AllocationAccessHooks CtfeProvenance Unit Unit Nat Unit := {
  resolvePointer := fun _ state pointer _ =>
    match pointer.provenance with
    | some provenance => ⟨state, .ok (.ok ⟨provenance.allocId, pointer.offset, ()⟩)⟩
    | none => ⟨state, .ok (.error pointer.offset.bytes)⟩
  beforeAllocationAccess := fun state _ => ⟨state, .ok ()⟩
  beforeMemoryRead := fun state extra _ _ _ _ => ⟨state, extra, .ok ()⟩
  beforeMemoryWrite := fun state extra _ _ _ _ =>
    ⟨state + 1, extra, if deny then .error "permission denied" else .ok ()⟩ }

private def dynamic : DynamicLayoutResolver CtfeProvenance Unit Unit Nat :=
  fun memory state _ => ⟨memory, state, .ok (some (sz 2, Align.ONE))⟩

private def initialized (allocation : Allocation CtfeProvenance Unit) (offset length : Nat) : Bool :=
  match allocation.initializationMask.isRangeInitialized (allocRange (sz offset) (sz length)) with
  | .ok (.ok ()) => true
  | _ => false

def main : IO Unit := do
  let some id := AllocId.ofUInt64 7 | throw (IO.userError "allocation ID")
  let .ok provenance := CtfeProvenance.fromAllocId id | throw (IO.userError "provenance")
  let .ok allocation := Allocation.fromBytes (Prov := CtfeProvenance) #[1,2,3,4] Align.ONE .Mut
    | throw (IO.userError "allocation")
  let issued := MemoryState.setIssuedIds (MemoryState.empty : MemoryState CtfeProvenance Unit Unit) #[id]
  let memory : MemoryState CtfeProvenance Unit Unit := {
    issued with live := #[(id, ⟨.stack, allocation⟩)] }
  let pointer := Pointer.new (some provenance) (sz 1)
  for sized in [true, false] do
    -- Unsized layouts carry no static extent: the two-byte range must come
    -- from the dynamic resolver, rather than accidentally matching size.
    let layout : MemoryOperandLayout := ⟨if sized then sz 2 else Size.ZERO,
      Align.ONE, .Memory (sized := sized), none⟩
    let place : MemoryOperandPlace CtfeProvenance := ⟨⟨pointer,.none,none⟩,layout⟩
    let result := writeUninitToMplace memory 0 place runtime false none globals (accesses false) dynamic
    check result.outcome.isOk "sized/unsized uninit write failed"
    check (result.hooks == 1) "uninit write skipped or duplicated permission hook"
    let some (_, entry) := result.memory.live[0]? | throw (IO.userError "live allocation")
    check (!initialized entry.allocation 1 2 && initialized entry.allocation 0 1 &&
      initialized entry.allocation 3 1) "uninit write did not preserve exact dynamic range"
    let denied := writeUninitToMplace memory 0 place runtime false none globals (accesses true) dynamic
    check (!denied.outcome.isOk && denied.hooks == 1) "permission failure or partial hook state lost"
    let some (_, entry) := denied.memory.live[0]? | throw (IO.userError "denied live allocation")
    check (initialized entry.allocation 0 4) "denied write changed initialized bytes"
    if !sized then
      let immediate := writeImmediateToMplaceNoValidate memory 0 .uninit place runtime false none
        globals (accesses false) dynamic (fun _ => false)
      check (immediate.outcome == .error .unsizedImmediateWrite)
        "dedicated uninit write must not relax immediate ABI assertions"
  let zero : MemoryOperandPlace CtfeProvenance :=
    ⟨⟨Pointer.new none (sz 1),.none,none⟩,⟨Size.ZERO,Align.ONE,.Memory (sized := true),none⟩⟩
  let result := writeUninitToMplace memory 0 zero runtime false none globals (accesses true) dynamic
  check (result.outcome.isOk && result.hooks == 0) "zero-sized write touched permission hooks"
  IO.println "PASS sized/unsized write_uninit, exact range, permission partial state and ZST"
