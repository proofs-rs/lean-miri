import duplicate_prefix.S02SameAllocationProtectSource

namespace DuplicatePrefix.S02SameAllocationProtectPacket
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Real return protection/uninit produces both source and return capabilities
on the SAME exact written allocation, from current disjoint-window data. -/
theorem invoke
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat) (before : Before) (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync,
      row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat+1 ≤ row.1.bytes.toNat)
    (source selected : Option UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (disjoint : input.offset.toNat+1 ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (sourcePositive : DuplicatePrefixBorrowAuthorization.Positive input.entry.allocation.extra input.tracker.global.protectedTags
      source selected maximum lower width) :
    let tree := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker input.tracker fresh)
      input.tracker.global.nextPointerTag
    let written := (tree.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    ∃ updated,
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag budget place
        (Storage.withCurrent frames frame before) =
        .ok () (S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated) ∧
      updated.extra = written ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive written global.protectedTags source selected maximum lower width) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts written global ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder written ∧
      ∃ child, written.indexOfTag input.tracker.global.nextPointerTag = some child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive written global.protectedTags
          (some child) input.selectedRoot input.maximum input.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin written child .Write input.offset (input.offset+1) := by
  have preserved := S02SameAllocationProtectSource.positive before place input runtime distinct order headroom fresh tag concrete
    source selected maximum lower width disjoint sourcePositive
  obtain ⟨updated,actual,extra,bytes,length,mutable,post,postOrder,child,tagged,positive,active⟩ :=
    S03ReturnProtectionRaw.invoke_concrete budget before model place input runtime distinct order headroom fresh tag concrete
      frames frame borrowFrame frameBorrow sync extras outside
  exact ⟨updated,actual,extra,bytes,length,mutable,preserved,post,postOrder,child,tagged,positive,active⟩

end
end DuplicatePrefix.S02SameAllocationProtectPacket

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SameAllocationProtectPacket.invoke) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
