import Miri.Interpreter.PointerMachine
import Miri.Interpreter.ExecutionChoices

/-! The same source address algorithm on the actual machine-only hook state.
Global allocation conversion cannot invent a MIR frame merely to adjust a
pointer. Source choices, address-map updates and reuse clock acquisition retain
exact ordering; the low-level GlobalAddressState algorithm remains shared. -/
namespace Miri.Interpreter.MachineAddress
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
abbrev State K U := MachineHooks.MachineState K (PointerMachine.User U)
abbrev M K U A := EStateM StepError (State K U) A
structure Hooks (K U : Type) where
  arithmetic : PointerArithmetic
  externalAddress : AllocId → AllocationAddressInfo → M K U UInt64
  classifyAddressError : AddressStateError → StepError
private def addresses : M K U GlobalAddressState := return (← get).user.addresses
private def setAddresses (value : GlobalAddressState) : M K U Unit :=
  modify fun state => {state with user := {state.user with addresses := value}}
private def finish (h : Hooks K U) (result : AddressStateResult A) : M K U A := do
  setAddresses result.state
  match result.outcome with
  | .ok value => pure value | .error error => throw (h.classifyAddressError error)
private def rate (access : ExecutionChoices.Access (State K U)) (site : ExecutionChoices.BoolSite)
    (probability : _root_.Float) : M K U Bool :=
  ExecutionChoices.bernoulli access site probability.toBits
private def slack (access : ExecutionChoices.Access (State K U)) : M K U (Fin 16) := do
  let selected ← ExecutionChoices.index access .addressSlack 16
  if valid : selected < 16 then pure ⟨selected,valid⟩
  else throw (.invalidProgram "checked address slack exceeded support")
open ExecutionChoices
def assign (h : Hooks K U) (id : AllocId)
    (kind : Option AddressMemoryKind) (choice : AddressRandomChoices) : M K U UInt64 := do
  let state ← addresses
  if let some cached := state.baseAddr.find? (fun entry => entry.allocId == id) then
    return cached.address
  let some kind := kind | throw (h.classifyAddressError (.missingMemoryKind id))
  let memory := (← get).memory
  let info ← match memory.getAllocInfo id with
    | .ok info => pure info
    | .error error => throw (.callback s!"address allocation metadata: {reprStr error}")
  let info : AllocationAddressInfo := {
    kind := if info.kind == .dead then .dead else if info.kind == .typeId then .typeId else .liveData
    live := memory.isAllocLive id
    size := info.size, align := info.align, memoryKind := some kind
    thread := UInt32.ofNat (← get).threads.activeThread.toNat }
  let external ← if state.addressMode != .managed && info.kind != .typeId && info.live then
      pure (some (← h.externalAddress id info)) else pure none
  -- Native address acquisition may install prepared backing in this same
  -- source address state. Cache against the updated state, retaining ownership.
  let current ← addresses
  let result := current.addrFromAllocId id (some info) choice ⟨external⟩
  let assignment ← finish h result
  match assignment with
  | .ready address => return address
  | .acquireRequired id address clock =>
    let machine ← get
    if let some global := machine.dataRace then
      match global.acquireClock machine.threads clock with
      | .error error => throw (.callback s!"address reuse clock acquisition: {reprStr error}")
      | .ok global => modify fun state => {state with dataRace := some global}
    let cached ← addresses
    finish h (cached.cacheAddress id address)
    return address

def addrFromAllocId (access : Access (State K U)) (h : Hooks K U)
    (id : AllocId) (kind : Option AddressMemoryKind) : M K U UInt64 := do
  let initial := (← get).user.addresses
  if let some cached := initial.baseAddr.find? (fun entry => entry.allocId == id) then return cached.address
  let some kind := kind | throw (h.classifyAddressError (.missingMemoryKind id))
  let state ← get
  let info ← match state.memory.getAllocInfo id with
    | .ok info => pure info
    | .error error => throw (.callback s!"address allocation metadata: {reprStr error}")
  if info.kind == .dead || !state.memory.isAllocLive id then
    throw (h.classifyAddressError (.deadAllocation id))
  let unused : AddressRandomChoices := ⟨false,false,0,⟨0,by decide⟩⟩
  if info.kind == .typeId || initial.addressMode != .managed then
    return ← assign h id (some kind) unused
  let some generation := initial.generation | throw (h.classifyAddressError .missingAddressGeneration)
  let reuse ← if kind == .stack then pure false else rate access .addressReuse generation.reusePool.addressReuseRate
  let cross ← if reuse then rate access .addressCrossThread generation.reusePool.addressReuseCrossThreadRate else pure false
  let prepared := generation.reusePool.prepareTakeAddr reuse cross info.size info.align kind
    (UInt32.ofNat (← get).threads.activeThread.toNat)
  setAddresses {initial with generation := some {generation with reusePool := prepared.state}}
  let range ← match prepared.outcome with
    | .ok range => pure range | .error error => throw (h.classifyAddressError (.reusePool error))
  let choices ← match range with
    | none => do
      let selected ← slack access
      pure {unused with reuse, crossThread := cross, slack := selected}
    | some (begin,stop) => do
      let selected ← index access .addressPool (stop-begin)
      pure {unused with reuse, crossThread := cross, poolIndex := begin+selected}
  assign h id (some kind) choices

end Miri.Interpreter.MachineAddress
