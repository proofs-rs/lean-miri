import empty_function.Specification
import empty_function.ChoiceExecution
namespace EmptyFunction.RawResources
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.Memory.AllocAddresses
open EmptyFunction.WholeCall
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- Registry data supplies metadata; it does not assert any materialization or
memory-operation success. Earlier registry branches may legitimately win. -/
theorem backing_info (before : State) (id : AllocId)
    (backing : InputDraft.MetadataBacking before id) :
    ∃ info, before.machine.memory.getAllocInfo id = .ok info := by
  cases result : before.machine.memory.getAllocInfo id with
  | ok info => exact ⟨info,rfl⟩
  | error error =>
    exfalso
    unfold MemoryState.getAllocInfo at result
    cases backing <;>
      simp only [MemoryState.hasExtraFunctionId,MemoryState.hasVaListId] at *
    all_goals
      repeat' first | (split at result) | contradiction
      all_goals simp_all [MemoryState.hasFunctionPointer]

theorem frontier (before : State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation) :
    ∀ row ∈ before.machine.user.addresses.intToPtrMap,
      row.address.toNat < generation.generator.nextBaseAddr.toNat := by
  intro row member
  obtain ⟨info,query⟩ := backing_info before row.allocId (representation.tables.suppliers row member)
  have prior := representation.allocatedBeforeCursor row member info query
  omega

/-- Actual allocator reservation is derived from the candidate's raw fields. -/
theorem reserve (p : Packet) (representation : InputDraft.AllocatorRepresentation p.before)
    (margins : Specification.AllocationMargins p) :
    ∃ after, p.before.machine.memory.reserveAllocId =
      (after,.ok ⟨p.before.machine.memory.nextAllocId,margins.nonzero⟩) :=
  MemoryState.reserve_of_highWater _ margins.available margins.nonzero
    margins.sourceAvailable margins.sourceNonzero representation.issued
    representation.live representation.global representation.dead

theorem fresh_base (before : State) (nonzero : before.machine.memory.nextAllocId ≠ 0)
    (highWater : ∀ row ∈ before.machine.user.addresses.baseAddr,
      row.allocId.value.toNat < before.machine.memory.nextAllocId.toNat) :
    before.machine.user.addresses.baseAddr.find?
      (fun row => row.allocId == (⟨before.machine.memory.nextAllocId,nonzero⟩ : AllocId)) = none := by
  apply Array.find?_eq_none.mpr
  intro row member
  intro equal
  have same := beq_iff_eq.mp equal
  have prior := highWater row member
  rw [same] at prior
  exact False.elim (Nat.lt_irrefl _ prior)
/-- Address-cache keys are runtime Memory.AllocIds issued by the same ledger;
compiler CTFE raw identities are deliberately absent from this condition. -/
theorem fresh_base_issued (before : State)
    (representation : InputDraft.AllocatorRepresentation before)
    (nonzero : before.machine.memory.nextAllocId ≠ 0) :
    before.machine.user.addresses.baseAddr.find?
      (fun row => row.allocId == (⟨before.machine.memory.nextAllocId,nonzero⟩ : AllocId)) = none :=
  fresh_base before nonzero (by
    intro row member
    exact representation.issued row.allocId (representation.basesIssued row member))

/-- Candidate numeric resources cover every legal stack slack. Size/alignment
bounds refer to the actual chosen local metadata, not an operation result. -/
theorem room (s : Static) (p : Packet) {choiceCondition : Prop} (resources : Specification.ResourceMargins s p choiceCondition)
    (generation : AddressGenerationState)
    (current : p.before.machine.user.addresses.generation = some generation)
    (size : Size) (align : Align)
    (alignment : InputDraft.AlignmentRepresentation align)
    (sizeBound : size.bytes.toNat ≤ resources.maximumSize)
    (alignBound : 2^align.pow2 ≤ resources.maximumAlignment)
    (one : 1 ≤ resources.budget) (slack : Fin 16) :
    RawGenerator.Room generation.generator size align slack := by
  obtain ⟨bytes,_,normalized⟩ := alignment
  have exponent := RawGenerator.normalized_exponent align bytes normalized
  have arithmetic := resources.addresses generation current
  apply RawGenerator.room_of_bounds generation.generator size align slack resources.budget
    resources.maximumSize resources.maximumAlignment one sizeBound
  · simpa only [RawGenerator.alignment_nat align exponent] using alignBound
  · exact arithmetic.arithmetic
  · exact arithmetic.capacity
/-- Candidate representation and numerical reserves discharge the real stack
address algorithm. Applying this after fresh parent allocation additionally
requires preservation of these raw facts through that allocation. -/
theorem stack_address (s : Static) (p : Packet) {choiceCondition : Prop}
    (resources : Specification.ResourceMargins s p choiceCondition)
    (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation p.before generation)
    (hooks : ChoiceExecution.H) (id : AllocId) (info : AllocationInfo)
    (missing : p.before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (metadata : p.before.machine.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData) (live : p.before.machine.memory.isAllocLive id = true)
    (noRace : p.before.machine.dataRace = none)
    (alignment : InputDraft.AlignmentRepresentation info.align)
    (sizeBound : info.size.bytes.toNat ≤ resources.maximumSize)
    (alignBound : 2^info.align.pow2 ≤ resources.maximumAlignment)
    (supply : ChoiceSupply.Environment ChoiceSupply.stackMissPlan
      (ChoiceExecution.tapeAccess.get p.before.machine)) :
    ∃ (value : Nat) (supported : value < 16) (after : ChoiceExecution.S),
      MachineAddress.addrFromAllocId ChoiceExecution.tapeAccess hooks id (some .stack) p.before.machine =
        .ok (RawGenerator.base generation.generator info.align ⟨value,supported⟩) after ∧
      ChoiceExecution.tapeAccess.get after = ChoiceSupply.advance
        (ChoiceExecution.tapeAccess.get p.before.machine)
        (.index .slack 16) (.index .addressSlack value) := by
  have minimum : 64 ≤ Specification.work s p := by
    unfold Specification.work
    omega
  have one : 1 ≤ resources.budget := by have := resources.reserve; omega
  have allRoom := room s p resources generation representation.current info.size info.align alignment
    sizeBound alignBound one
  obtain ⟨bytes,_,normalized⟩ := alignment
  exact ChoiceExecution.stack_success_from_environment hooks p.before.machine id info generation
    missing metadata data live representation.managed representation.current noRace
    (RawGenerator.normalized_exponent info.align bytes normalized)
    allRoom
    (resources.addresses generation representation.current).positiveCursor
    (frontier p.before generation representation) supply
end EmptyFunction.RawResources
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.RawResources." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved raw address proof axiom {dependency} in {name}"
