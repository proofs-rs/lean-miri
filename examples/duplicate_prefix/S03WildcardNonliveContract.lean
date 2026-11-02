import duplicate_prefix.S03WildcardNonliveCallEquality
import duplicate_prefix.S03WildcardNonliveInput
import duplicate_prefix.S03NonliveContract
import duplicate_prefix.S03MaterializableInput

namespace DuplicatePrefix.S03WildcardNonliveContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification DuplicatePrefixEmptyReferenceInput S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Every count and return provenance for a selected supported nonlive
wildcard hit, including exact-base and interior addresses. The original
Candidate supplies address coherence/liveness; actual argument normalization
proves same-state call equality before reusing the concrete nonlive Result.
No resolver success, canonical destination or final permission is a premise. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : pointer.provenance = .wildcard)
    (hit : S03WildcardEmptyClassification.Hit (imageContext options before input.contract.tracker)
      before.memory before.user.addresses pointer.offset.bytes)
    (metadata : Metadata before.memory hit.id none)
    (absent : before.memory.live.find? (fun row => row.1 == hit.id) = none)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  let tag := input.contract.destination.tracker.global.nextPointerTag
  let synthetic := S03WildcardNonliveInput.concrete_input input wildcard hit metadata absent tag
  let facts := S03NonliveCallResources.of_contract synthetic hit.id tag rfl
  have metadataSome := S03NonliveMetadataTag.changeTag before.memory hit.id none (some tag) metadata absent
  obtain ⟨installed,done,entry,trace,terminal,empty,noErrors,noUb,prefixSuccess⟩ :=
    S03NonliveContract.complete synthetic hit.id tag rfl metadataSome absent count
  obtain ⟨info,known,nonlive⟩ := S03NonliveEmptyMetadata.known before.memory hit.id none metadata absent
  have sameInfo : info = hit.info := Except.ok.inj (known.symm.trans hit.known)
  have notData : hit.info.kind ≠ .liveData := sameInfo ▸ nonlive
  have candidate := S03WildcardEmptyClassification.candidate input.contract wildcard
  have allocLive : before.memory.isAllocLive hit.id = true :=
    candidate.2.coherent.live.2 hit.id (Array.contains_iff_mem.mp hit.exposed)
  let offset := pointer.offset.bytes-hit.base
  have address : hit.base+offset = pointer.offset.bytes := by rw [UInt64.add_comm];exact UInt64.sub_add_cancel _ _
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span
    input.contract.model.preciseOff input.contract.model.implicitOff
  have equal := S03WildcardNonliveCallEquality.call_equal options limits remaining span ctx
    input.contract.model.debugOff input.contract.model.nullComparator facts.dynamicFuel facts.validityFuel
    facts.dynamicEq facts.validityEq hit.id tag input.contract.destination.tracker hit.base offset count
    (by rw [address];exact candidate.1) before input.contract.model.ghostOff input.contract.model.shallow hit.cached
    hit.info hit.known notData (by rw [address];exact hit.geometry) candidate.2.nonstrict hit.exposed allocLive
    input.contract.destination.enabled facts.first input.contract.model.noDataRace input.contract.model.metadata
    input.slice_not_constructed place input.contract.thread input.contract.active input.contract.emptyHarnessCache
  have original : Pointer.new .wildcard (Size.ofBytes (hit.base+offset)) = pointer := by
    rw [address]
    change (⟨pointer.offset,.wildcard⟩ : Pointer Provenance) = pointer
    rw [←wildcard]
  have concrete : Pointer.new (.concrete hit.id tag) (Size.ofBytes (hit.base+offset)) =
      S03WildcardNonliveInput.concretePointer pointer hit.id tag := by rw [address];rfl
  refine ⟨installed,done,?_,trace,terminal,empty,noErrors,noUb,prefixSuccess⟩
  simp only [original,concrete] at equal
  have originalCall := equal.trans entry
  simpa only [DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue] using originalCall

/-- After this Candidate-driven dispatch, selected hits retain only live or
image alternatives. Every supported nonlive branch finishes internally; the
miss is an initial classifier result for the separate miss family. -/
theorem dispatch {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : pointer.provenance = .wildcard) (count : UInt64) :
    before.user.addresses.allocIdFromAddr pointer.offset.bytes 0 (GlobalAddressLiveErrorExclusion.lookup before.memory) = .ok none ∨
    (∃ hit : S03WildcardEmptyClassification.Hit (imageContext options before input.contract.tracker)
        before.memory before.user.addresses pointer.offset.bytes,
      (∃ entry, before.memory.live.find? (fun row => row.1 == hit.id) = some (hit.id,entry)) ∨
      (Materializable (imageContext options before input.contract.tracker) before.memory before.user.addresses hit.id none ∧
        Nonempty (S03MaterializableInput.Packet options before input.contract.tracker hit.id none))) ∨
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  rcases S03WildcardEmptyClassification.contract input.contract wildcard with miss | hits
  · exact Or.inl miss
  · obtain ⟨hit⟩ := hits
    rcases hit.target with known | image
    · cases known with
      | live entry present parent => exact Or.inr (Or.inl ⟨hit,Or.inl ⟨entry,present⟩⟩)
      | functionRow absent present =>
        exact Or.inr (Or.inr (complete input wildcard hit (.functionRow absent present) absent count))
      | vaListRow absent noFunction present =>
        exact Or.inr (Or.inr (complete input wildcard hit (.vaListRow absent noFunction present) absent count))
      | nondataGlobal descriptor absent noFunction noVaList present kind =>
        exact Or.inr (Or.inr (complete input wildcard hit (.nondataGlobal descriptor absent noFunction noVaList present kind) absent count))
      | dead entry absent noFunction noVaList noGlobal present =>
        exact Or.inr (Or.inr (complete input wildcard hit (.dead entry absent noFunction noVaList noGlobal present) absent count))
    · exact Or.inr (Or.inl ⟨hit,Or.inr ⟨image,S03MaterializableInput.of_input options before input.contract.tracker hit.id none
        image input.contract.resources.cachedRootsBelow⟩⟩)

end
end DuplicatePrefix.S03WildcardNonliveContract
