import Miri.Input.CompilerInitialAllocationAtomicBytes
import Miri.Input.CompilerInitialAllocationStore
import Miri.Interpreter.MachineHooks
import Miri.Interpreter.GlobalByteMachine

/-! Actual machine-state provider. Missing typed state is Unsupported. The
current machine memory and authoritative store commit together EVEN ON ERROR,
so consumed shared source IDs cannot vanish behind an Except result. -/
namespace Miri.Input.CompilerInitialAllocation.ByteMachine
open Miri.Memory Miri.ABI Miri.Interpreter
set_option autoImplicit false
variable {K User O U : Type}
structure Access (User : Type) where
  getStore : User → Option Store
  setStore : Store → User → User
  /-- Required law for concrete User-field adapters; not a no-op setter. -/
  get_set : ∀ store user, getStore (setStore store user) = some store

def reserve (access : Access User) (target : TargetDataLayout) (run : Nat)
    (bytes : Array UInt8) (salt : UInt64) : MachineHooks.M K User AllocId := do
  let state ← get
  let some store := access.getStore state.machine.user
    | throw (.unsupported "complete initial typed compiler-global store is not attached")
  let (outcome,world) := AtomicBytes.reserve target run bytes salt (store.withMemory state.machine.memory)
  let user := access.setStore world.store state.machine.user
  set {state with machine := {state.machine with memory := world.memory,user := user}}
  match outcome with
  | .ok id => pure id
  | .error error => throw (.unsupported error)

def bytes (access : Access User) (target : TargetDataLayout) (run : Nat)
    (functions : FunctionPointers.Hooks K User O) (value : Array UInt8) : MachineHooks.M K User (Pointer Provenance) := do
  let salt ← functions.chooseSalt
  let id ← reserve access target run value (UInt64.ofNat salt.val)
  FunctionPointers.rootPointer functions id

def string [DecidableEq K] (store : Access (ValidityMachine.UserState U)) (target : TargetDataLayout) (run : Nat)
    (functions : FunctionPointers.Hooks K (ValidityMachine.UserState U) O)
    (access : ValidityMachine.Access K U) (strLayout : ValidityMachine.M K U LocalLayout) (value : String) :
    ValidityMachine.M K U (MPlaceTy Provenance) := do
  let data := value.toUTF8.data
  let pointer ← bytes store target run functions data
  if data.size >= 2^64 then throw (.invalidProgram "string length exceeds source u64 conversion")
  let length ← match Scalar.fromUInt (BitVec.ofNat 128 data.size) access.runtime.pointerOffset with
    | .ok value => pure value | .error error => throw (ScalarOps.scalarError error)
  let layout ← strLayout
  PointerPlaceMachine.withMetadata access pointer.withOptionalProvenance (.metadata length) layout false

/-- Explicit profile dispatch; no initially-empty or stale legacy cache can
stand in for an installed complete initial typed store. -/
def reserveCurrent (access : Access User) (target : TargetDataLayout)
    (value : Array UInt8) (salt : UInt64) : MachineHooks.M K User AllocId := do
  match (← get).machine.memory.activeInitialCompilerRun with
  | some run => reserve access target run value salt
  | none =>
    if bound : salt.toNat < 32 then GlobalByteMachine.reserve value ⟨salt.toNat,bound⟩
    else throw (.unsupported "legacy byte provider salt outside captured Fin32 domain")
def bytesCurrent (access : Access User) (target : TargetDataLayout)
    (functions : FunctionPointers.Hooks K User O) (value : Array UInt8) : MachineHooks.M K User (Pointer Provenance) := do
  match (← get).machine.memory.activeInitialCompilerRun with
  | some run => bytes access target run functions value
  | none => GlobalByteMachine.bytes functions value
def stringCurrent [DecidableEq K] (store : Access (ValidityMachine.UserState U)) (target : TargetDataLayout)
    (functions : FunctionPointers.Hooks K (ValidityMachine.UserState U) O)
    (access : ValidityMachine.Access K U) (strLayout : ValidityMachine.M K U LocalLayout) (value : String) :
    ValidityMachine.M K U (MPlaceTy Provenance) := do
  match (← get).machine.memory.activeInitialCompilerRun with
  | some run => string store target run functions access strLayout value
  | none => GlobalByteMachine.string functions access strLayout value
end Miri.Input.CompilerInitialAllocation.ByteMachine
