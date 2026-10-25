import Miri.Interpreter.MemoryOperand

open Miri.ABI Miri.Memory Miri.Interpreter

private structure Hooks where
  events : Array String := #[]
  deriving DecidableEq, Repr

private def event (state : Hooks) (name : String) : Hooks :=
  { state with events := state.events.push name }

private def machineOk (state : Hooks) (value : α) : MachineHookResult Hooks α :=
  ⟨state, .ok value⟩

private def globalHooks : GlobalAllocationHooks CtfeProvenance Unit Unit Hooks := {
  synchronizeMemory := fun _ state => state
  evaluateStaticInitializer := fun memory state _ => ⟨memory, state, .error "unused"⟩
  beforeAccessGlobal := fun memory state _ _ _ _ => ⟨memory, state, .ok ()⟩
  adjustGlobalAllocation := fun memory state _ allocation =>
    ⟨memory, state, .ok (.borrowed allocation)⟩
}

private def accessHooks : AllocationAccessHooks CtfeProvenance Unit Unit Hooks Unit := {
  resolvePointer := fun _ state pointer _ =>
    let state := event state "resolve"
    match pointer.provenance with
    | some provenance => ⟨state, .ok (.ok ⟨provenance.allocId, pointer.offset, ()⟩)⟩
    | none => ⟨state, .ok (.error pointer.offset.bytes)⟩
  beforeAllocationAccess := fun state _ => machineOk (event state "beforeAllocAccess") ()
  beforeMemoryRead := fun state extra _ _ _ _ =>
    ⟨event state "beforeMemoryRead", extra, .ok ()⟩
  beforeMemoryWrite := fun state extra _ _ _ _ =>
    ⟨event state "beforeMemoryWrite", extra, .ok ()⟩
}

private def dynamicLayout : DynamicLayoutResolver CtfeProvenance Unit Unit Hooks :=
  fun memory hooks _ => ⟨memory, hooks, .ok none⟩

private def testRuntime : RuntimeTargetDataLayout :=
  { RuntimeTargetDataLayout.default with base := ⟨.little, .w64⟩ }

private def sz (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)
private def range (start finish : Nat) : AllocRange := allocRange (sz start) (sz (finish - start))

private def scalarInt (value : Nat) (bytes : Nat) : Except ScalarError (Scalar CtfeProvenance) :=
  Scalar.fromUInt (BitVec.ofNat 128 value) (sz bytes)

private def scalarAbi (integer : Integer) (size : Size) : IO Miri.ABI.Scalar := do
  let validRange ← match WrappingRange.full size with
    | .ok range => pure range
    | .error _ => throw (IO.userError "ABI range failed")
  pure (.Initialized (value := .Int integer false) (validRange := validRange))

private def requireAlloc {Extra : Type} (result : EStateM.Result AllocError
    (Allocation CtfeProvenance Extra) Unit) : IO (Allocation CtfeProvenance Extra) := do
  match result with
  | .ok () allocation => pure allocation
  | .error error _ => throw (IO.userError s!"allocation setup failed: {error}")

private def requireResult (result : Except ε α) (context : String) : IO α := do
  match result with
  | .ok value => pure value
  | .error _ => throw (IO.userError context)

private def pointerFor (id : AllocId) (offset : Size) : IO (Pointer (Option CtfeProvenance)) := do
  let provenance ← match CtfeProvenance.fromAllocId id with
    | .ok value => pure value
    | .error _ => throw (IO.userError "could not create test provenance")
  pure (Pointer.new (some provenance) offset)

private def makeFixture (initialBytes : Array UInt8) : IO
    (MemoryState CtfeProvenance Unit Unit × AllocId × Pointer (Option CtfeProvenance)) := do
  let id ← match AllocId.ofUInt64 7 with
    | some id => pure id
    | none => throw (IO.userError "could not create test allocation ID")
  let allocation ← match Allocation.fromBytes initialBytes Align.ONE .Mut with
    | .ok allocation => pure allocation
    | .error error => throw (IO.userError s!"allocation setup failed: {error}")
  let empty : MemoryState CtfeProvenance Unit Unit := MemoryState.empty
  let issued := MemoryState.setIssuedIds empty #[id]
  let memory : MemoryState CtfeProvenance Unit Unit := {
    issued with live := #[(id, ⟨.stack, allocation⟩)] }
  let pointer ← pointerFor id Size.ZERO
  pure (memory, id, pointer)

private def hexDigit (value : Nat) : Char :=
  if value < 10 then Char.ofNat (48 + value)
  else Char.ofNat (87 + value)

private def littleHex (bytes : Array UInt8) : String := Id.run do
  let mut output := ""
  for byte in bytes do
    let value := byte.toNat
    output := output.push (hexDigit (value / 16))
    output := output.push (hexDigit (value % 16))
  return output

private def isAllInitialized (allocation : Allocation CtfeProvenance Unit)
    (range : AllocRange) : IO Bool := do
  match allocation.initializationMask.isRangeInitialized range with
  | .ok (.ok ()) => pure true
  | .ok (.error _) => pure false
  | .error reason => throw (IO.userError s!"init-mask query failed: {reason}")

private def placeFor (pointer : Pointer (Option CtfeProvenance))
    (layout : MemoryOperandLayout) : MemoryOperandPlace CtfeProvenance :=
  ⟨⟨pointer, .none, none⟩, layout⟩

private def runWrite (memory : MemoryState CtfeProvenance Unit Unit)
    (pointer : Pointer (Option CtfeProvenance)) (layout : MemoryOperandLayout)
    (value : Immediate CtfeProvenance) (laterValidate : Bool) :
    MemoryOperandResult CtfeProvenance Unit Unit Hooks Unit :=
  writeImmediateToMplaceNoValidate memory {} value (placeFor pointer layout)
    testRuntime false none globalHooks accessHooks dynamicLayout (fun _ => laterValidate)

private def emitResult (tag : String)
    (result : MemoryOperandResult CtfeProvenance Unit Unit Hooks Unit) : IO Unit := do
  match result.outcome with
  | .error error => IO.println s!"W {tag} error={repr error}"
  | .ok () =>
    let some (_, entry) := result.memory.live[0]?
      | throw (IO.userError "test allocation disappeared")
    let bytes ← requireResult (entry.allocation.getBytesUnchecked (range 0 24))
      "test byte read failed"
    let allInit ← isAllInitialized entry.allocation (range 0 24)
    let gapInit ← isAllInitialized entry.allocation (range 8 16)
    let ptrs := String.intercalate "," <| entry.allocation.provenanceMap.ptrs.toList.map
      fun (offset, _) => toString offset.bytes.toNat
    IO.println s!"W {tag} ok bytes={littleHex bytes} all_init={allInit} gap_init={gapInit} ptrs={ptrs}"

def main : IO Unit := do
  let i64Abi ← scalarAbi .I64 (sz 8)
  let ptrAbi := Miri.ABI.Scalar.Initialized (value := .Pointer AddressSpace.ZERO)
      (validRange := (← match WrappingRange.full (sz 8) with
        | .ok value => pure value
        | .error _ => throw (IO.userError "pointer ABI range failed")))
  let layout : MemoryOperandLayout := {
    size := sz 24
    align := Align.ONE
    backendRepr := .ScalarPair (a := i64Abi) (b := ptrAbi) (bOffset := sz 16)
  }
  let (memory, id, pointer) ← makeFixture (Array.replicate 24 0)
  let some (_, initialEntry) := memory.live[0]?
    | throw (IO.userError "test allocation is absent")
  let initial ← requireAlloc <| Allocation.writeScalar testRuntime.base (range 8 16)
    (← match scalarInt 0xfeedface 8 with
      | .ok value => pure value
      | .error reason => throw (IO.userError s!"integer setup failed: {reason}"))
    initialEntry.allocation
  let initial ← requireAlloc <| Allocation.writeScalar testRuntime.base (range 16 24)
    (← match scalarInt 0x1122334455667788 8 with
      | .ok value => pure value
      | .error reason => throw (IO.userError s!"integer setup failed: {reason}")) initial
  let seeded := { memory with live := #[(id, ⟨.stack, initial⟩)] }
  let pointerProv ← match CtfeProvenance.fromAllocId id with
    | .ok value => pure value
    | .error _ => throw (IO.userError "could not create pointer provenance")
  let pointerScalar := Scalar.fromPointer testRuntime.base
      (Pointer.new pointerProv (sz 0x1234))
  let first ← match scalarInt 0xaabbccdd 8 with
    | .ok value => pure value
    | .error reason => throw (IO.userError s!"first scalar setup failed: {reason}")
  let value := Immediate.scalarPair first pointerScalar
  let result := runWrite seeded pointer layout value false
  emitResult "padded_pair" result

