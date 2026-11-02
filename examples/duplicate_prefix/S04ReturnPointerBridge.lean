import duplicate_prefix.DuplicatePrefixCallSpecification
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowPointerChecks
namespace DuplicatePrefix.S04ReturnPointerBridge
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open CanonicalConfigFacts
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
/-- The raw return-place data supplies the REAL canonical
input.pointer-resolution and dereference checks. Neither success equation is an
input. The target input.pointer, allocation, offset and initial machine state are
unchanged. The destination byte need not be initialized. This is not a proof of
construction of the whole-call Initial record. -/
theorem concrete (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (state : RootState)
    (place : MPlaceTy Provenance)
    (model : DuplicatePrefixCallModel.Model options remaining span state.machine)
    (input : DuplicatePrefixReturnPlaceInput.Input state.machine place)
    (id : AllocId) (tag : BorTag) (provenance : input.pointer.provenance = .concrete id tag) :
    id = input.id ∧ ∃ anchor,
      input.source = some anchor ∧ input.entry.allocation.extra.indexOfTag tag = some anchor ∧
      (PreparedContracts.actualConfig options () remaining span).retag.resolveAllocation
        input.pointer.withOptionalProvenance state =
        .ok (some ⟨input.id,Size.ofBytes input.offset,.concrete tag⟩) state ∧
      (PreparedContracts.actualConfig options () remaining span).retag.checkPtrAccess
        input.pointer.withOptionalProvenance (Size.ofBytes (1 : UInt64)) state = .ok () state := by
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
  obtain ⟨same,anchor,source,tagged⟩ := binding
  have offset : input.pointer.offset = Size.ofBytes (input.base+input.offset) := by
    change Size.ofBytes input.pointer.offset.bytes = Size.ofBytes (input.base+input.offset)
    exact congrArg Size.ofBytes input.pointerAddress
  have encoded : input.pointer.withOptionalProvenance =
      Pointer.new (some (.concrete input.id tag)) (Size.ofBytes (input.base+input.offset)) := by
    simp only [Pointer.withOptionalProvenance,Pointer.new,offset,provenance,same]
  let ctx := Classical.choice ((DuplicatePrefixCallModel.contexts options remaining span state.machine model).2.2.1)
  refine ⟨same,anchor,source,tagged,?_,?_⟩
  · rw [ctx.source.resolve,encoded]
    exact RetagPointerChecks.resolve_allocation_cached ctx.pointers state input.id tag input.base input.offset ctx.arithmetic input.cachedBase
  · rw [ctx.source.check,encoded]
    apply RetagPointerChecks.check_pointer_access_cached ctx.pointers _ state input.id tag input.base input.offset (1 : UInt64) input.entry ctx.resolve ctx.arithmetic input.cachedBase input.live
    · exact UInt64.lt_iff_toNat_lt.mpr (by decide : 0 < (1 : UInt64).toNat)
    · exact (by decide : (1 : UInt64).toNat < 9223372036854775808)
    · simpa [input.size,Size.ofBytes] using input.bounds
/-- The wildcard branch derives the SAME canonical checks from the existing
raw inverse-map geometry/exposure data, not a successful lookup premise. -/
theorem wildcard (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (state : RootState)
    (place : MPlaceTy Provenance)
    (model : DuplicatePrefixCallModel.Model options remaining span state.machine)
    (input : DuplicatePrefixReturnPlaceInput.Input state.machine place)
    (provenance : input.pointer.provenance = .wildcard) :
    input.source = none ∧
      (PreparedContracts.actualConfig options () remaining span).retag.resolveAllocation
        input.pointer.withOptionalProvenance state =
        .ok (some ⟨input.id,Size.ofBytes input.offset,.wildcard⟩) state ∧
      (PreparedContracts.actualConfig options () remaining span).retag.checkPtrAccess
        input.pointer.withOptionalProvenance (Size.ofBytes (1 : UInt64)) state = .ok () state := by
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
  obtain ⟨source,mode,exposed,geometry⟩ := binding
  rw [input.pointerAddress] at geometry
  have offset : input.pointer.offset = Size.ofBytes (input.base+input.offset) := by
    change Size.ofBytes input.pointer.offset.bytes = Size.ofBytes (input.base+input.offset)
    exact congrArg Size.ofBytes input.pointerAddress
  have encoded : input.pointer.withOptionalProvenance =
      Pointer.new (some .wildcard) (Size.ofBytes (input.base+input.offset)) := by
    simp only [Pointer.withOptionalProvenance,Pointer.new,offset,provenance]
  let ctx := Classical.choice ((DuplicatePrefixCallModel.contexts options remaining span state.machine model).2.2.1)
  refine ⟨source,?_,?_⟩
  · rw [ctx.source.resolve,encoded]
    have resolved := WildcardGeneralHitReborrow.resolve ctx.pointers state (input.base+input.offset) input.base input.id input.entry geometry ctx.arithmetic mode exposed input.cachedBase input.live
    simpa only [UInt64.add_comm input.base input.offset,UInt64.add_sub_cancel] using resolved
  · rw [ctx.source.check,encoded]
    apply GeneralBorrowPositiveWildcardWindowPointerChecks.check ctx.pointers _ state input.base input.offset (1 : UInt64) input.id input.entry geometry ctx.resolve ctx.arithmetic mode exposed input.cachedBase input.live
    · exact UInt64.lt_iff_toNat_lt.mpr (by decide : 0 < (1 : UInt64).toNat)
    · exact (by decide : (1 : UInt64).toNat < 9223372036854775808)
    · simpa [input.size,Size.ofBytes] using input.bounds


/-- The real physical destination pointer passes canonical resolution and
one-byte access checks, without assuming its old byte is initialized. -/
theorem from_input (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (state : RootState)
    (place : MPlaceTy Provenance)
    (model : DuplicatePrefixCallModel.Model options remaining span state.machine)
    (input : DuplicatePrefixReturnPlaceInput.Input state.machine place) :
    ∃ extra,
      (PreparedContracts.actualConfig options () remaining span).retag.resolveAllocation
        place.mplace.ptr state = .ok (some ⟨input.id,Size.ofBytes input.offset,extra⟩) state ∧
      (PreparedContracts.actualConfig options () remaining span).retag.checkPtrAccess
        place.mplace.ptr (Size.ofBytes 1) state = .ok () state := by
  rw [input.physicalPointer]
  cases provenance : input.pointer.provenance with
  | concrete id tag =>
    obtain ⟨_,anchor,_,_,resolved,checked⟩ := concrete options remaining span state place model input id tag provenance
    exact ⟨.concrete tag,resolved,checked⟩
  | wildcard =>
    obtain ⟨_,resolved,checked⟩ := wildcard options remaining span state place model input provenance
    exact ⟨.wildcard,resolved,checked⟩

end
end DuplicatePrefix.S04ReturnPointerBridge
