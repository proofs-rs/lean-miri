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
  let memory : MemoryState CtfeProvenance Unit Unit := {
    empty with
    live := #[(id, ⟨.stack, allocation⟩)]
  } |>.setIssuedIds #[id]
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


private def assertCheck (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

example : (Scalar.fromInt (Prov := CtfeProvenance) 0 (sz 1)).map Scalar.size = .ok (sz 1) := by decide
example : (Scalar.nullPointer (Prov := CtfeProvenance) testRuntime.base).map Scalar.size = .ok (sz 8) := by decide

def main : IO Unit := do
  for (n,integer) in #[(1,Integer.I8),(4,Integer.I32),(8,Integer.I64),(16,Integer.I128)] do
    let abi ← scalarAbi integer (sz n)
    let layout : MemoryOperandLayout := ⟨sz n,Align.ONE,.Scalar abi,none⟩
    let (memory,_,pointer) ← makeFixture (Array.replicate n 0xaa)
    let old ← requireResult (Scalar.nullPointer (Prov := CtfeProvenance) testRuntime.base) "old scalar setup"
    let oldResult := runWrite memory pointer layout (.scalar old) false
    if n != 8 then
      assertCheck (oldResult.outcome == .error (.immediateSizeMismatch (sz n) (sz 8))) s!"old width mismatch not reproduced at{n}"
      assertCheck oldResult.hooks.events.isEmpty "ABI failure reached memory access"
    let fixed ← requireResult (Scalar.fromInt (Prov := CtfeProvenance) 0 layout.size) "new scalar setup"
    assertCheck (!fixed.isPointer && fixed.size == sz n) "destination zero size/provenance wrong"
    let result := runWrite memory pointer layout (.scalar fixed) false
    assertCheck (result.outcome == .ok ()) s!"destination sizedzero failed at{n}: {repr result.outcome}"
    let some (_,entry) := result.memory.live[0]? | throw (IO.userError "live allocation missing")
    let bytes ← requireResult (entry.allocation.getBytesUnchecked (range 0 n)) "read written bytes"
    assertCheck (bytes.all (· == 0)) "destination not overwritten with zero"
    assertCheck (← isAllInitialized entry.allocation (range 0 n)) "zero write left uninitialized bytes"
    let invalidLayout := {layout with backendRepr := .Memory (sized := true)}
    let rejected := runWrite memory pointer invalidLayout (.scalar fixed) false
    assertCheck (rejected.outcome == .error .immediateAbiMismatch && rejected.hooks.events.isEmpty) "nonscalar ABI guard weakened"
  IO.println "PASS destination-sized zero widths1/4/8/16, original mismatch, unchanged ABI guard and write effects"
