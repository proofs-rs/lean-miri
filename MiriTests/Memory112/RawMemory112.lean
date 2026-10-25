import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.MemoryShims
import Miri.Memory.MiriMemoryKind

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
open Miri.MIR

private abbrev K := MiriMemoryKind
private abbrev User := Unit
private abbrev State := MachineHooks.State K User
private abbrev Machine := MachineHooks.MachineState K User
private abbrev AccessState := PlaceMachine.AccessState K User

private def globalHooks : GlobalAllocationHooks Provenance BorrowTree K AccessState := {
  synchronizeMemory := fun _ state => state
  evaluateStaticInitializer := fun memory state _ => ⟨memory, state, .error "unused"⟩
  beforeAccessGlobal := fun memory state _ _ _ _ => ⟨memory, state, .ok ()⟩
  adjustGlobalAllocation := fun memory state _ _ => ⟨memory, state, .error "unused"⟩
}

private def config : PlaceMachine.AccessConfig K User := {
  runtime := { RuntimeTargetDataLayout.default with base := ⟨.little, .w64⟩ }
  ghostMode := false
  globalKind := none
  globalHooks
  dynamicLayout := fun memory state _ => ⟨memory, state, .ok none⟩
  resolvePointer := fun _ pointer _ machine =>
    match pointer.provenance with
    | some (.concrete id tag) => .ok (.ok ⟨id, pointer.offset, .concrete tag⟩) machine
    | _ => .ok (.error pointer.offset.bytes) machine
  beforeAllocationAccess := fun _ => pure ()
  diagnostic := fun _ _ _ => pure ()
  weakMemoryWrite := fun _ _ => pure ()
  syncAccess := fun _ _ _ => pure ()
  retainTouched := fun machine _ => machine
  memoryError := fun error => .invalidProgram (reprStr error)
}

private def sz (n : Nat) := Size.ofBytes (UInt64.ofNat n)
private def run (action : MachineHooks.M K User A) (state : State) : IO (State × A) := do
  match MachineHooks.run action state with
  | (state, .ok value) => pure (state, value)
  | (_, .error error) => throw (IO.userError (reprStr error))
private def hasError : Except ε α → Bool
  | .ok _ => false
  | .error _ => true
private def allocationBytes (allocation : Allocation Provenance BorrowTree) : IO (Array UInt8) := do
  match allocation.getBytesUnchecked (allocRange Size.ZERO allocation.byteSize) with
  | .ok bytes => pure bytes
  | .error error => throw (IO.userError (toString error))

private def initial (mutability : Miri.Memory.Mutability) : IO (State × Pointer (Option Provenance) × AllocId) := do
  let some id := AllocId.ofUInt64 7 | throw (IO.userError "invalid allocation ID")
  let some tag := BorTag.ofUInt64 1 | throw (IO.userError "invalid borrow tag")
  let tree := BorrowTree.new tag (sz 16)
  let mut allocation ← match Allocation.fromBytes (Prov := Provenance) (Array.replicate 16 0) Align.ONE .Mut with
    | .ok value => pure (value.withExtra tree)
    | .error error => throw (IO.userError (toString error))
  let provenance := Provenance.concrete id tag
  let scalar := Scalar.fromPointer config.runtime.base (Pointer.new provenance (sz 4))
  match Allocation.writeScalar config.runtime.base (allocRange (sz 0) (sz 8)) scalar allocation with
  | .ok () updated => allocation := updated
  | .error error _ => throw (IO.userError (toString error))
  allocation := allocation.withMutability mutability
  let emptyMemory : MemoryState Provenance BorrowTree K := MemoryState.empty
  let memory0 := MemoryState.setIssuedIds emptyMemory #[id]
  let memory : MemoryState Provenance BorrowTree K := {
    memory0 with live := #[(id, ⟨.machine .machine, allocation⟩)] }
  let machine : Machine := {
    memory, borrowTracker := none, dataRace := none, threads := .initial false
    raceAllocations := #[], allocationSpans := #[], user := () }
  pure (⟨Stack.empty, machine⟩, Pointer.new (some provenance) Size.ZERO, id)

private def allocationAt (state : State) (id : AllocId) : IO (Allocation Provenance BorrowTree) := do
  let some (_, entry) := state.machine.memory.live.find? (·.1 == id)
    | throw (IO.userError "allocation disappeared")
  pure entry.allocation

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def dummyLayout : TyAndLayout TyId := ⟨0, {
  fields := .Primitive, variants := .Single 0, backendRepr := .Memory (sized := true),
  largestNiche := none, uninhabited := false, align := .new Align.ONE,
  size := Size.ZERO, maxReprAlign := none, unadjustedAbiAlign := Align.ONE,
  reprC := false, randomizationSeed := 0 }⟩
private def dummyArg : ArgAbi TyId := ⟨dummyLayout, .Ignore⟩
private def memsetAbi : FnAbi TyId := {
  args := #[dummyArg, dummyArg, dummyArg], ret := dummyArg, cVariadic := false,
  fixedCount := 3, conv := .C, canUnwind := false }

private def foreignCore (pointer : Pointer (Option Provenance)) (byte : Int32) (count : UInt64) : ForeignItems.Core
    Provenance State Unit Unit (Pointer (Option Provenance)) (Pointer (Option Provenance)) Unit := {
  family := .unix, os := "linux", arch := "x86_64", maximumSize := 1024,
  noAllocShimSymbol := "__no_alloc_shim_is_unstable", allocatorSymbol := fun _ => pure none,
  lookupFunction := fun _ => pure none, forceAllocation := pure,
  returnToBlock := fun _ => pure (), unwindToBlock := fun _ => pure (),
  nativeEnabled := false, callNative := fun _ _ _ => pure false,
  expectedAbi := fun _ => pure memsetAbi, argumentCompat := fun _ _ => pure true,
  checkSymbolClash := fun _ => pure (), transmute := fun operand _ => pure operand,
  readUsize := fun _ => pure count, readPointer := fun _ => pure pointer,
  readI32 := fun _ => pure byte, isNull := fun _ => pure false,
  allocate := fun _ _ _ _ => throw (.unsupported "unused memset allocation"),
  deallocate := fun _ _ _ => throw (.unsupported "unused memset deallocation"),
  reallocate := fun _ _ _ _ _ => throw (.unsupported "unused memset reallocation"),
  writePointer := fun _ _ => pure (), writeNull := fun _ => pure (),
  setEnomem := pure (), startExit := fun _ => pure (), specialDestination := pure }

private def shimHooks (pointer : Pointer (Option Provenance)) (byte : Int32) (count : UInt64) : MemoryShims.CoreHooks
    Provenance State Unit Unit (Pointer (Option Provenance)) Unit := {
  foreign := foreignCore pointer byte count
  checkPointer := RawMemoryMachine.checkPointer config
  readByte := RawMemoryMachine.readByte config ⟨sz 8⟩
  readBytes := RawMemoryMachine.readBytes config ⟨sz 8⟩
  offset := fun pointer amount => match RawMemoryMachine.offset ⟨sz 8⟩ pointer amount with
    | .ok pointer => pure pointer | .error error => throw error
  copy := fun _ _ _ _ => throw (.unsupported "unused memset copy")
  writeRepeatedByte := RawMemoryMachine.writeRepeatedByte config ⟨sz 8⟩
  writeI32 := fun _ _ => pure ()
  writeUsize := fun _ _ => pure ()
  wcharLayout := throw (.unsupported "unused wchar layout")
  checkAlignment := fun _ _ => throw (.unsupported "unused alignment")
  readUnsigned := RawMemoryMachine.readUnsigned config ⟨sz 8⟩ }

def main : IO Unit := do
  let (start, pointer, id) ← initial .Mut
  let (written, _) ← run (RawMemoryMachine.writeRepeatedByte config ⟨sz 8⟩ pointer 0xA5 4) start
  let allocation ← allocationAt written id
  ensure ((← allocationBytes allocation) == #[0xA5,0xA5,0xA5,0xA5,0,0,0,0,0,0,0,0,0,0,0,0]) "repeated fill bytes differ"
  ensure (allocation.provenanceMap.getPtr Size.ZERO == none) "overwritten pointer provenance survived"
  ensure (match allocation.initializationMask.isRangeInitialized (allocRange Size.ZERO (sz 4)) with
    | .ok (.ok ()) => true | _ => false) "fill left init range unchecked"
  let (memsetState, result) ← run (MemoryShims.Source.emulate (shimHooks pointer 0x1A3 4) 0 "memset" memsetAbi
    #[⟨.immediate .uninit, dummyLayout⟩, ⟨.immediate .uninit, dummyLayout⟩,
      ⟨.immediate .uninit, dummyLayout⟩] ()) written
  ensure (result == some .NeedsReturn) "MemoryShims.memset did not return normally"
  let memsetAllocation ← allocationAt memsetState id
  ensure ((← allocationBytes memsetAllocation).extract 0 4 == #[0xA3,0xA3,0xA3,0xA3]) "memset did not truncate/fill bytes"
  let hugeMemset := MachineHooks.run (MemoryShims.Source.emulate (shimHooks pointer 0 18446744073709551615)
    0 "memset" memsetAbi #[⟨.immediate .uninit, dummyLayout⟩, ⟨.immediate .uninit, dummyLayout⟩,
      ⟨.immediate .uninit, dummyLayout⟩] ()) memsetState
  ensure (hasError hugeMemset.2) "memset with huge count succeeded"
  ensure ((← allocationBytes (← allocationAt hugeMemset.1 id)) == (← allocationBytes memsetAllocation)) "huge memset changed bytes before bounds failure"
  let beforeHuge := ← allocationBytes allocation
  let huge := MachineHooks.run (RawMemoryMachine.writeRepeatedByte config ⟨sz 8⟩ pointer 0 18446744073709551615) written
  let afterHuge := huge.1
  ensure (hasError huge.2) "huge UInt64 count succeeded"
  ensure ((← allocationBytes (← allocationAt afterHuge id)) == beforeHuge) "huge count modified bytes before bounds failure"
  let outOfBounds := MachineHooks.run (RawMemoryMachine.writeRepeatedByte config ⟨sz 8⟩ pointer 0 17) written
  ensure (hasError outOfBounds.2) "out-of-bounds repeated fill succeeded"
  ensure ((← allocationBytes (← allocationAt outOfBounds.1 id)) == beforeHuge) "out-of-bounds fill modified bytes"
  let (partialStart, partialPointer, partialId) ← initial .Mut
  let partialRange := allocRange Size.ZERO (sz 4)
  let partialResult := MachineHooks.run (RawMemoryMachine.writeBytes config ⟨sz 32⟩
    partialPointer ⟨#[1,2,3,4]⟩) partialStart
  ensure (hasError partialResult.2) "inconsistent pointer-layout partial write unexpectedly succeeded"
  let partialAllocation ← allocationAt partialResult.1 partialId
  ensure (partialAllocation.provenanceMap.getPtr Size.ZERO == some (match partialPointer.provenance with
    | some (.concrete _ tag) => Provenance.concrete partialId tag | _ => .wildcard))
    "partial provenance error did not retain map state"
  ensure (match partialAllocation.initializationMask.isRangeInitialized partialRange with
    | .ok (.ok ()) => true | _ => false) "partial error did not retain initialization"
  let (readonly, readPointer, readonlyId) ← initial .Not
  let beforeReadonly ← allocationBytes (← allocationAt readonly readonlyId)
  let failedReadonly := MachineHooks.run (RawMemoryMachine.writeRepeatedByte config ⟨sz 8⟩ readPointer 9 1) readonly
  ensure (hasError failedReadonly.2) "readonly write succeeded"
  ensure ((← allocationBytes (← allocationAt failedReadonly.1 readonlyId)) == beforeReadonly) "readonly write changed bytes"
  let (zeroed, _, zeroId) ← initial .Not
  let (zeroResult, _) ← run (RawMemoryMachine.writeRepeatedByte config ⟨sz 8⟩ (Pointer.new none Size.ZERO) 9 0) zeroed
  ensure ((← allocationBytes (← allocationAt zeroResult zeroId)) == (← allocationBytes (← allocationAt zeroed zeroId))) "zero length changed bytes"
  IO.println "source112 connected RawMemoryMachine fill checks passed"
