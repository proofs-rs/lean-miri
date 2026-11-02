import empty_function.ProjectedAddress
import empty_function.PolicyChoiceExecution
namespace EmptyFunction.ProjectedPolicyAddress
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open EmptyFunction.WholeCall EmptyFunction.PolicyChoiceSupply
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem stack (hooks : ChoiceProjection.H) (state : State) (id : AllocId)
    (info : AllocationInfo) (generation : AddressGenerationState)
    (missing : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : state.machine.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : state.machine.memory.isAllocLive id = true)
    (managed : state.machine.user.addresses.addressMode = .managed)
    (current : state.machine.user.addresses.generation = some generation)
    (alignment : info.align.pow2 ≤ 29) (room : ∀ slack, RawGenerator.Room generation.generator info.size info.align slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (frontier : ∀ row ∈ state.machine.user.addresses.intToPtrMap,
      row.address.toNat < generation.generator.nextBaseAddr.toNat)
    (supply : PolicyChoiceSupply.Environment ChoiceSupply.stackMissPlan (ChoiceProjection.tapeAccess.get state)) :
    ∃ (value : Nat) (supported : value < 16) (nextTape : ExecutionChoices.Tape) (addresses : GlobalAddressState),
      PolicyStep (.index .slack 16) (ChoiceProjection.tapeAccess.get state) (.index .addressSlack value) nextTape ∧
      ExecutionAddressChoices.addrFromAllocId ChoiceProjection.tapeAccess hooks id (some .stack) state =
        .ok (RawGenerator.base generation.generator info.align ⟨value,supported⟩)
          (ProjectedAddress.assigned (ChoiceProjection.tapeAccess.put state nextTape) addresses) ∧
      addresses.baseAddr.find? (fun row => row.allocId == id) =
        some ⟨id,RawGenerator.base generation.generator info.align ⟨value,supported⟩⟩ ∧
      addresses = (ProjectedAddress.stackAttempt state id info.size info.align ⟨value,supported⟩).state ∧
      (ProjectedAddress.stackAttempt state id info.size info.align ⟨value,supported⟩).outcome =
        .ok (.ready (RawGenerator.base generation.generator info.align ⟨value,supported⟩)) := by
  obtain ⟨input,support,nextTape,step,tail⟩ := supply.fits
  cases support with
  | index kind count value supported =>
    have laws : AccessLaws ChoiceProjection.tapeAccess := ⟨by intros; rfl,by intros; rfl⟩
    have draw := PolicyChoiceExecution.index_policyStep ChoiceProjection.tapeAccess laws state
      (ChoiceProjection.tapeAccess.get state) nextTape .slack 16 value rfl supported step
    obtain ⟨addresses,actual,cached,addressState,addressReady⟩ := ProjectedAddress.stack_after_index hooks state id info generation
      missing metadata data live managed current alignment room positive frontier value supported nextTape draw
    exact ⟨value,supported,nextTape,addresses,step,actual,cached,addressState,addressReady⟩
end EmptyFunction.ProjectedPolicyAddress
