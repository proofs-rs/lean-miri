import duplicate_prefix.S05ConcreteEntryBridge
import duplicate_prefix.S05PositivePointerBridge
import duplicate_prefix.S05ConsistentCallSpecification

namespace DuplicatePrefix.S02PositiveInitBridge
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification
open CanonicalConfigFacts
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- The positive concrete caller's stored initial reference supplies both
real pointer checks and the actual protected FnEntry borrowing operation.
The operation is on the exact initial tree and global tracker; it is not yet
the typed MIR `Call.initStackFrame` or the physical return-slot update. -/
theorem concrete_entry
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (frame : FrameState) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (raw : GeneralBorrowRawFnEntry.Input reference.entry.allocation.extra reference.tracker.global)
      (output : GeneralBorrowForestFnEntry.Output),
      id = reference.id ∧ raw.parentTag = tag ∧ raw.offset = reference.offset ∧ raw.len = len ∧
      (PreparedContracts.actualConfig options () remaining span).retag.resolveAllocation
        (Pointer.new (some (.concrete id tag)) (Size.ofBytes address)) (⟨⟨#[]⟩,before⟩ : RootState) =
        .ok (some ⟨reference.id,Size.ofBytes reference.offset,.concrete tag⟩) ⟨⟨#[]⟩,before⟩ ∧
      (PreparedContracts.actualConfig options () remaining span).retag.checkPtrAccess
        (Pointer.new (some (.concrete id tag)) (Size.ofBytes address)) (Size.ofBytes len)
        (⟨⟨#[]⟩,before⟩ : RootState) = .ok () ⟨⟨#[]⟩,before⟩ ∧
      GeneralBorrowForestFnEntry.operation reference.entry.allocation.extra reference.tracker.global
        frame reference.id raw.parentTag raw.offset raw.len .VisitChildrenOfAccessed = .ok output ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      ∃ child, output.child.tree.indexOfTag output.tag = some child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive output.child.tree output.global.protectedTags
          (some child) (some raw.selected) raw.maximum raw.offset raw.len) := by
  obtain ⟨reference,same,raw,parentTag,offset,length,source,selected,maximum,runtime⟩ :=
    S05ConcreteEntryBridge.from_contract id tag address len input.contract nonempty
  obtain ⟨_,_,_,_,resolved,checked⟩ :=
    S05PositivePointerBridge.concrete options remaining span (⟨⟨#[]⟩,before⟩ : RootState)
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len input.contract.model reference id tag rfl
  obtain ⟨output,actual,_,_,_,access,constructed,afterRuntime,_,_,child,present,_,capability,_⟩ :=
    GeneralBorrowRawFnEntry.invoke_positive reference.entry.allocation.extra reference.tracker.global
      frame reference.id runtime raw
  refine ⟨reference,raw,output,same,parentTag,offset,length,?_,?_,actual,access,constructed,
    afterRuntime,child,present,capability⟩
  · simpa only [Pointer.withOptionalProvenance,Pointer.new] using resolved
  · simpa only [Pointer.withOptionalProvenance,Pointer.new] using checked

/-- If the positive argument and destination are in the same allocation,
the caller's absolute-address separation translates to disjoint allocation
offsets. This is the physical fact needed to preserve the argument while the
destination byte is protected and uninitialized. -/
theorem same_allocation_disjoint
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {len : UInt64} {place : MPlaceTy Provenance}
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      argument len place) (nonempty : len ≠ 0) :
    ∃ (pointer : Pointer Provenance) (reference : DuplicatePrefixReferenceInput.Positive before pointer len),
      argument = .pointer pointer ∧
      (reference.id = input.contract.destination.id →
        reference.offset.toNat + len.toNat ≤ input.contract.destination.offset.toNat ∨
        input.contract.destination.offset.toNat + 1 ≤ reference.offset.toNat) := by
  cases input.contract.reference with
  | empty zero _ => exact False.elim (nonempty zero)
  | positive pointer encoding reference =>
    refine ⟨pointer,reference,encoding,?_⟩
    intro same
    let destination := input.contract.destination
    change reference.offset.toNat + len.toNat ≤ destination.offset.toNat ∨
      destination.offset.toNat + 1 ≤ reference.offset.toNat
    have bases := Option.some.inj (reference.cachedBase.symm.trans (same ▸ destination.cachedBase))
    have baseEq : reference.base = destination.base :=
      congrArg Miri.Memory.AllocAddresses.BaseAddressEntry.address bases
    have sourceFits : reference.base.toNat + reference.offset.toNat < 2^64 := by
      have bounds := reference.storage.bounds
      have fits := reference.addressFits
      omega
    have sourceAddress : pointer.offset.bytes.toNat = reference.base.toNat + reference.offset.toNat := by
      rw [reference.pointerAddress,UInt64.toNat_add,Nat.mod_eq_of_lt sourceFits]
    have targetAddress := destination.address_interval.1
    have argumentAddress : DuplicatePrefixSliceArgument.address argument = pointer.offset.bytes := by
      rw [encoding]
      rfl
    rcases input.contract.separated with zero | left | right
    · exact False.elim (nonempty zero)
    · rw [argumentAddress] at left
      change pointer.offset.bytes.toNat + len.toNat ≤ destination.pointer.offset.bytes.toNat at left
      rw [sourceAddress,targetAddress,baseEq] at left
      exact Or.inl (by omega)
    · rw [argumentAddress] at right
      change destination.pointer.offset.bytes.toNat + 1 ≤ pointer.offset.bytes.toNat at right
      rw [sourceAddress,targetAddress,baseEq] at right
      exact Or.inr (by omega)

end
end DuplicatePrefix.S02PositiveInitBridge
