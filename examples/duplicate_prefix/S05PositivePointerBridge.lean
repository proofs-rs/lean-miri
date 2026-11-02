import duplicate_prefix.DuplicatePrefixCallSpecification
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowPointerChecks
namespace DuplicatePrefix.S05PositivePointerBridge
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open CanonicalConfigFacts
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
/-- The proposed call-time positive-reference data supplies the REAL canonical
pointer-resolution and dereference checks. Neither success equation is an
input. The target pointer, allocation, offset and initial machine state are
unchanged. This is one S05 bridge, not a proof of ordinary-valid coverage or
construction of the whole-call Initial record. -/
theorem concrete (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (state : RootState)
    (pointer : Pointer Provenance) (len : UInt64)
    (model : DuplicatePrefixCallModel.Model options remaining span state.machine)
    (input : DuplicatePrefixReferenceInput.Positive state.machine pointer len)
    (id : AllocId) (tag : BorTag) (provenance : pointer.provenance = .concrete id tag) :
    id = input.id ∧ ∃ anchor,
      input.source = some anchor ∧ input.entry.allocation.extra.indexOfTag tag = some anchor ∧
      (PreparedContracts.actualConfig options () remaining span).retag.resolveAllocation
        pointer.withOptionalProvenance state =
        .ok (some ⟨input.id,Size.ofBytes input.offset,.concrete tag⟩) state ∧
      (PreparedContracts.actualConfig options () remaining span).retag.checkPtrAccess
        pointer.withOptionalProvenance (Size.ofBytes len) state = .ok () state := by
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
  obtain ⟨same,anchor,source,tagged⟩ := binding
  have offset : pointer.offset = Size.ofBytes (input.base+input.offset) := by
    change Size.ofBytes pointer.offset.bytes = Size.ofBytes (input.base+input.offset)
    exact congrArg Size.ofBytes input.pointerAddress
  have encoded : pointer.withOptionalProvenance =
      Pointer.new (some (.concrete input.id tag)) (Size.ofBytes (input.base+input.offset)) := by
    simp only [Pointer.withOptionalProvenance,Pointer.new,offset,provenance,same]
  let ctx := Classical.choice ((DuplicatePrefixCallModel.contexts options remaining span state.machine model).2.2.1)
  refine ⟨same,anchor,source,tagged,?_,?_⟩
  · rw [ctx.source.resolve,encoded]
    exact RetagPointerChecks.resolve_allocation_cached ctx.pointers state input.id tag input.base input.offset ctx.arithmetic input.cachedBase
  · rw [ctx.source.check,encoded]
    apply RetagPointerChecks.check_pointer_access_cached ctx.pointers _ state input.id tag input.base input.offset len input.entry ctx.resolve ctx.arithmetic input.cachedBase input.live
    · exact UInt64.lt_iff_toNat_lt.mpr input.storage.positive
    · exact input.storage.signedSize
    · simpa only [input.size,Size.ofBytes] using input.storage.bounds
/-- The wildcard branch derives the SAME canonical checks from the existing
raw inverse-map geometry/exposure data, not a successful lookup premise. -/
theorem wildcard (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (state : RootState)
    (pointer : Pointer Provenance) (len : UInt64)
    (model : DuplicatePrefixCallModel.Model options remaining span state.machine)
    (input : DuplicatePrefixReferenceInput.Positive state.machine pointer len)
    (provenance : pointer.provenance = .wildcard) :
    input.source = none ∧
      (PreparedContracts.actualConfig options () remaining span).retag.resolveAllocation
        pointer.withOptionalProvenance state =
        .ok (some ⟨input.id,Size.ofBytes input.offset,.wildcard⟩) state ∧
      (PreparedContracts.actualConfig options () remaining span).retag.checkPtrAccess
        pointer.withOptionalProvenance (Size.ofBytes len) state = .ok () state := by
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
  obtain ⟨source,mode,exposed,geometry⟩ := binding
  rw [input.pointerAddress] at geometry
  have offset : pointer.offset = Size.ofBytes (input.base+input.offset) := by
    change Size.ofBytes pointer.offset.bytes = Size.ofBytes (input.base+input.offset)
    exact congrArg Size.ofBytes input.pointerAddress
  have encoded : pointer.withOptionalProvenance =
      Pointer.new (some .wildcard) (Size.ofBytes (input.base+input.offset)) := by
    simp only [Pointer.withOptionalProvenance,Pointer.new,offset,provenance]
  let ctx := Classical.choice ((DuplicatePrefixCallModel.contexts options remaining span state.machine model).2.2.1)
  refine ⟨source,?_,?_⟩
  · rw [ctx.source.resolve,encoded]
    have resolved := WildcardGeneralHitReborrow.resolve ctx.pointers state (input.base+input.offset) input.base input.id input.entry geometry ctx.arithmetic mode exposed input.cachedBase input.live
    simpa only [UInt64.add_comm input.base input.offset,UInt64.add_sub_cancel] using resolved
  · rw [ctx.source.check,encoded]
    apply GeneralBorrowPositiveWildcardWindowPointerChecks.check ctx.pointers _ state input.base input.offset len input.id input.entry geometry ctx.resolve ctx.arithmetic mode exposed input.cachedBase input.live
    · exact UInt64.lt_iff_toNat_lt.mpr input.storage.positive
    · exact input.storage.signedSize
    · simpa only [input.size,Size.ofBytes] using input.storage.bounds

/-- Exhaustive positive-provenance split for this existing call-time candidate.
This proves real pointer leaves, not whole-call Target or ordinary-valid coverage. -/
theorem positive (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (state : RootState)
    (pointer : Pointer Provenance) (len : UInt64)
    (model : DuplicatePrefixCallModel.Model options remaining span state.machine)
    (input : DuplicatePrefixReferenceInput.Positive state.machine pointer len) :
    ∃ extra,
      (PreparedContracts.actualConfig options () remaining span).retag.resolveAllocation
        pointer.withOptionalProvenance state = .ok (some ⟨input.id,Size.ofBytes input.offset,extra⟩) state ∧
      (PreparedContracts.actualConfig options () remaining span).retag.checkPtrAccess
        pointer.withOptionalProvenance (Size.ofBytes len) state = .ok () state := by
  cases provenance : pointer.provenance with
  | concrete id tag =>
    obtain ⟨_,anchor,_,_,resolved,checked⟩ := concrete options remaining span state pointer len model input id tag provenance
    exact ⟨.concrete tag,resolved,checked⟩
  | wildcard =>
    obtain ⟨_,resolved,checked⟩ := wildcard options remaining span state pointer len model input provenance
    exact ⟨.wildcard,resolved,checked⟩

/-- Direct positive branch of the EXISTING provisional Contract. No extra
resolution/access/context certificate is supplied by the caller. The Contract
itself still has the explicitly documented normalization/coverage limitations. -/
theorem from_contract (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (state : RootState)
    (argument : DuplicatePrefixSliceArgument.Argument) (len : UInt64) (place : MPlaceTy Provenance)
    (contract : DuplicatePrefixCallSpecification.LegacyContract options limits remaining span state.machine argument len place)
    (nonzero : len ≠ 0) :
    ∃ (pointer : Pointer Provenance) (input : DuplicatePrefixReferenceInput.Positive state.machine pointer len),
      argument = .pointer pointer ∧ ∃ extra,
      (PreparedContracts.actualConfig options () remaining span).retag.resolveAllocation
        (DuplicatePrefixSliceArgument.placePointer argument) state =
        .ok (some ⟨input.id,Size.ofBytes input.offset,extra⟩) state ∧
      (PreparedContracts.actualConfig options () remaining span).retag.checkPtrAccess
        (DuplicatePrefixSliceArgument.placePointer argument) (Size.ofBytes len) state = .ok () state := by
  cases contract.reference with
  | empty zero metadata => exact False.elim (nonzero zero)
  | positive pointer encoding input =>
    obtain ⟨extra,resolved,checked⟩ := positive options remaining span state pointer len contract.model input
    refine ⟨pointer,input,encoding,extra,?_,?_⟩
    · simpa only [encoding,DuplicatePrefixSliceArgument.placePointer] using resolved
    · simpa only [encoding,DuplicatePrefixSliceArgument.placePointer] using checked

end
end DuplicatePrefix.S05PositivePointerBridge
