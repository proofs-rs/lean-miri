import Miri.Interpreter.NativePreparedGlobals
import Miri.Interpreter.MachineAddress

/-! Component-only ownership fixture. Deterministic buffer identity models an
external backing capability; no host allocation, byte-copy, or Rust execution
claim is made. NativePreparedGlobals.reserve and both actual address caches run. -/
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
private abbrev Machine := MachineAddress.State Unit Nat
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def backing : NativeAllocationLifecycle.Backing Machine where
  isolated := true
  zeroed := fun size align => do
    let bytes ← NativeAllocationLifecycle.alignmentBytes align
    modify fun state => {state with user := {state.user with payload := state.user.payload + 1}}
    pure (some ⟨4096,⟨size.bytes.toNat,bytes⟩⟩)
  fromBytes := fun _ _ => throw (.unsupported "unused component backing fromBytes")
  copyInto := fun _ _ => throw (.unsupported "unused component backing copy")
  snapshot := fun _ => throw (.unsupported "unused component backing snapshot")
  release := fun _ => throw (.unsupported "unexpected component backing release")
private def external (id : AllocId) (info : AllocationAddressInfo) : MachineAddress.M Unit Nat UInt64 := do
  pure (UInt64.ofNat (← NativePreparedGlobals.reserve NativePreparedGlobals.machineAccess backing id info.size info.align))
private def machineHooks : MachineAddress.Hooks Unit Nat := {
  arithmetic := ⟨Size.ofBytes 8⟩
  externalAddress := external
  classifyAddressError := fun error => .invalidProgram (toString error) }
private def pointerHooks : PointerMachine.Hooks Unit Nat := {
  arithmetic := machineHooks.arithmetic
  externalAddress := fun id info => NativeAllocationLifecycle.liftMachineAction (external id info)
  ensureTreeExtra := fun _ => throw (.unsupported "unused component tree materialization")
  diagnosticIntToPtr := throw (.unsupported "unused component pointer diagnostic")
  strictIntToPtr := .machineStop "Int2PtrWithStrictProvenance"
  classifyAddressError := machineHooks.classifyAddressError }
private def assertRetained (state : Machine) (id : AllocId) : IO Unit := do
  check (state.user.payload == 1) "cached lookup reacquired external backing"
  let some (_,prepared) := state.user.addresses.preparedNativeBytes.find? (·.1 == id)
    | throw (IO.userError "address cache erased prepared native ownership")
  check (prepared.owner.pointer == 4096 && prepared.owner.isolated && prepared.size == Size.ofBytes 8)
    "prepared native owner changed"
  check ((state.user.addresses.baseAddr.find? (·.allocId == id)).map (·.address) == some 4096)
    "native base address was not cached"
private def must (result : EStateM.Result StepError S A) : IO (A × S) :=
  match result with
  | .ok value state => pure (value,state)
  | .error error _ => throw (IO.userError (reprStr error))
def main : IO Unit := do
  let some id := AllocId.ofUInt64 1 | throw (IO.userError "invalid fixture ID")
  let addresses ← match GlobalAddressState.new .default .nativeLib 0 18446744073709551615 ⟨0.5,0.1⟩ with
    | .ok value => pure value | .error error => throw (IO.userError (toString error))
  let memory : MemoryState Provenance BorrowTree MiriMemoryKind :=
    MemoryState.setGlobalEntries MemoryState.empty
      #[⟨id,.memory,Size.ofBytes 8,Align.ONE,.Not,none⟩]
  let state : Machine := {
    memory
    borrowTracker := none, dataRace := none, threads := .initial false
    raceAllocations := #[], allocationSpans := #[], user := ⟨addresses,0,#[]⟩ }
  let choices : AddressRandomChoices := ⟨false,false,0,⟨0,by decide⟩⟩
  let (value,after) ← must (MachineAddress.assign machineHooks id (some .other) choices state)
  check (value == 4096) "machine address changed backing identity"
  assertRetained after id
  let (_,cached) ← must (MachineAddress.assign machineHooks id none choices after)
  assertRetained cached id
  let full : PointerMachine.State Unit Nat := ⟨⟨#[]⟩,state⟩
  let (value,after) ← must (PointerMachine.addrFromAllocId pointerHooks id (some .other) choices full)
  check (value == 4096) "pointer address changed backing identity"
  assertRetained after.machine id
  let (_,cached) ← must (PointerMachine.addrFromAllocId pointerHooks id none choices after)
  assertRetained cached.machine id
  IO.println "component ownership: MachineAddress and PointerMachine retain prepared native registry through first assignment and cache hit"
