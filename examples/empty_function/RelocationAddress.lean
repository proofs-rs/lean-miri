import empty_function.ReuseAssign
import empty_function.ChoiceExecution
namespace EmptyFunction.RelocationAddress
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Internal effectful adapter. The completed pure fact is proved from raw
current inputs in the public theorem below, not required by ValidInput. -/
private theorem assign_completed (hooks : ChoiceExecution.H) (state : ChoiceExecution.S)
    (id : AllocId) (info : AllocationInfo) (choices : AddressRandomChoices)
    (uncached : state.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId) (live : state.memory.isAllocLive id = true)
    (managed : state.user.addresses.addressMode = .managed) (noRace : state.dataRace = none)
    (completed : ∃ next, AddressChoicePlan.assignedState
      (state.user.addresses.addrFromAllocId id (some {
        kind := .liveData, live := true, size := info.size, align := info.align,
        memoryKind := some .other, thread := UInt32.ofNat state.threads.activeThread.toNat }) choices) = .ok next) :
    ∃ value after, MachineAddress.assign hooks id (some .other) choices state = .ok value after ∧
      after.memory = state.memory ∧ after.borrowTracker = state.borrowTracker ∧
      after.threads = state.threads ∧ after.user.payload = state.user.payload := by
  let addrInfo : AllocationAddressInfo := {
    kind := .liveData, live := true, size := info.size, align := info.align,
    memoryKind := some .other, thread := UInt32.ofNat state.threads.activeThread.toNat }
  cases outcome : state.user.addresses.addrFromAllocId id (some addrInfo) choices ⟨none⟩ with
  | mk afterAddress result =>
    simp only [addrInfo] at outcome
    simp only [outcome,AddressChoicePlan.assignedState] at completed
    cases result with
    | error error => simp at completed
    | ok assignment =>
      cases assignment with
      | ready address =>
        unfold MachineAddress.assign
        unfold_machine_address_helpers
        simp [uncached,metadata,notDead,notType,live,managed,noRace,outcome,
          get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
          modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
        exact ⟨address,_,⟨rfl,rfl⟩,rfl,rfl,rfl,rfl⟩
      | acquireRequired target address clock =>
        cases cached : afterAddress.cacheAddress target address with
        | mk cacheState result =>
          simp only [cached] at completed
          cases result with
          | error error => simp at completed
          | ok value =>
            cases value
            unfold MachineAddress.assign
            unfold_machine_address_helpers
            simp [uncached,metadata,notDead,notType,live,managed,noRace,outcome,cached,
              get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
              modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
            exact ⟨address,_,⟨rfl,rfl⟩,rfl,rfl,rfl,rfl⟩

/-- Actual nonstack assignment for every supported reuse/cross/range response
from a current nonempty candidate bucket. Root generation and tape requests
are separate source prefixes; no address success is an input hypothesis. -/
theorem reuse_assignment (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (hooks : ChoiceExecution.H) (id : AllocId) (info : AllocationInfo)
    (bucket : Array ReusableAddress) (cross : Bool) (selection : Nat)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : before.machine.memory.getAllocInfo id = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId) (live : before.machine.memory.isAllocLive id = true)
    (noRace : before.machine.dataRace = none)
    (present : generation.reusePool.pool[info.align.pow2]? = some bucket)
    (alignment : InputDraft.AlignmentRepresentation info.align)
    (reuseSupport : ChoiceSupply.Supported (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits)
      (.boolean .addressReuse true))
    (crossSupport : ChoiceSupply.Supported (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits)
      (.boolean .addressCrossThread cross))
    (lower : (ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).1 ≤ selection)
    (upper : selection < (ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).2) :
    ∃ value after, MachineAddress.assign hooks id (some .other)
      ⟨true,cross,selection,⟨0,by decide⟩⟩ before.machine = .ok value after ∧
      after.memory = before.machine.memory ∧ after.borrowTracker = before.machine.borrowTracker ∧
      after.threads = before.machine.threads ∧ after.user.payload = before.machine.user.payload := by
  apply assign_completed hooks before.machine id info _ uncached metadata notDead notType live
    representation.managed noRace
  exact ReuseAssign.current_pool before generation representation id _ bucket cross selection
    uncached rfl rfl rfl present alignment reuseSupport crossSupport lower upper
theorem reuse_assignment_at (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (hooks : ChoiceExecution.H) (state : ChoiceExecution.S)
    (addressesSame : state.user.addresses = before.machine.user.addresses)
    (threadSame : state.threads.activeThread = before.machine.threads.activeThread)
    (id : AllocId) (info : AllocationInfo)
    (bucket : Array ReusableAddress) (cross : Bool) (selection : Nat)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.memory.getAllocInfo id = .ok info)
    (notDead : info.kind ≠ .dead) (notType : info.kind ≠ .typeId) (live : state.memory.isAllocLive id = true)
    (noRace : state.dataRace = none)
    (present : generation.reusePool.pool[info.align.pow2]? = some bucket)
    (alignment : InputDraft.AlignmentRepresentation info.align)
    (reuseSupport : ChoiceSupply.Supported (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits)
      (.boolean .addressReuse true))
    (crossSupport : ChoiceSupply.Supported (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits)
      (.boolean .addressCrossThread cross))
    (lower : (ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).1 ≤ selection)
    (upper : selection < (ReuseCandidate.candidate bucket info.size (UInt32.ofNat before.machine.threads.activeThread.toNat) cross).2) :
    ∃ value after, MachineAddress.assign hooks id (some .other)
      ⟨true,cross,selection,⟨0,by decide⟩⟩ state = .ok value after ∧
      after.memory = state.memory ∧ after.borrowTracker = state.borrowTracker ∧
      after.threads = state.threads ∧ after.user.payload = state.user.payload := by
  apply assign_completed hooks state id info _ (by simpa only [addressesSame] using uncached)
    metadata notDead notType live (by simpa only [addressesSame] using representation.managed) noRace
  have completed := ReuseAssign.current_pool before generation representation id
    (⟨.liveData,true,info.size,info.align,some .other,UInt32.ofNat before.machine.threads.activeThread.toNat⟩ : AllocationAddressInfo)
    bucket cross selection uncached rfl rfl rfl present alignment reuseSupport crossSupport lower upper
  simpa only [addressesSame,threadSame] using completed

end EmptyFunction.RelocationAddress
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationAddress.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation address axiom {dependency} in {name}"
