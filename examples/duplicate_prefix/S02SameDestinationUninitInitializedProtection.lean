import duplicate_prefix.S03ReturnProtectionRaw
import duplicate_prefix.S02SameDestinationUninitInitializedWrite

namespace DuplicatePrefix.S02SameDestinationUninitInitializedProtection
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual configured return protection plus uninit write, using only
residual local bounds after argument FnEntry. Its literal tree definitions
allow other observers' derived facts to be transported to the same result. -/
theorem invoke_concrete
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
      row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat+1 ≤ row.1.bytes.toNat) :
    let tree := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker input.tracker fresh)
      input.tracker.global.nextPointerTag
    let written := (tree.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    ∃ updated,
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag budget place
        (Storage.withCurrent frames frame before) =
        .ok () (S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated) ∧
      input.entry.allocation.initializationMask.setRange
        (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) false = .ok updated.initializationMask ∧
      ProvenanceMap.clear (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1))
        (AllocationCopy.snapshot input.entry.allocation) (Size.ofBytes 8) input.entry.allocation.provenanceMap =
          .ok () updated.provenanceMap ∧
      updated.extra = written ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      InitMaskCopy.WellFormed updated.initializationMask ∧
      updated.initializationMask.len = input.entry.allocation.initializationMask.len ∧
      (∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts written global ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder written ∧
      ∃ child, written.indexOfTag input.tracker.global.nextPointerTag = some child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive written global.protectedTags
          (some child) input.selectedRoot input.maximum input.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin written child .Write input.offset (input.offset+1) := by
  obtain ⟨actual,post,capacity,short,roots,postOrder,child,tagged,⟨positive⟩,active⟩ :=
    S03ReturnProtectionRaw.retag budget before model place input runtime distinct order headroom fresh tag concrete frames frame borrowFrame frameBorrow
  let tree := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1
  let current := ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree
  let next := S04ReturnRetaggedInput.from_borrowed input frames frame borrowFrame fresh tree child input.selectedRoot
    input.maximum tagged capacity positive
  obtain ⟨updated,write,maskEq,extra,bytes,length,mutable,maskWf,maskLen,clearEq,pointers,afterRuntime,afterTags,afterOrder,afterPositive,afterActive⟩ :=
    S02SameDestinationUninitInitializedWrite.from_current (options := options) (remaining := remaining) span current _ next post roots postOrder
      short input.tracker.global.nextPointerTag rfl model.noDataRace model.noBackend sync extras outside
  let after := S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated
  have configuredWrite : (config options remaining span).retag.writeUninit
      (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag) current = .ok () after := by
    obtain ⟨ctx⟩ := ActualRetagContext.exists_context options remaining span model.preciseOff model.implicitOff
    rw [ctx.construction]
    change (do
      let access ← ValidityMachine.scopedAccess (config options remaining span).access
      PlaceMachine.writeMemory access (fun _ => false) .uninit
        (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag)) current = .ok () after
    have accessGhost : (config options remaining span).access.ghostMode = false := by
      rw [(DuplicatePrefixPhysicalContexts.canonical options remaining span).accessEq]
      rfl
    have scope := S04ProtectUninitWrite.scopedAccess_of_not_ghost
      (config options remaining span).access current accessGhost model.ghostOff
    simp only [bind,EStateM.bind,scope]
    exact write
  refine ⟨updated,?_,maskEq,clearEq,extra,bytes,length,mutable,maskWf,maskLen,pointers,afterRuntime,afterOrder,child,?_,afterPositive,afterActive child active⟩
  · unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
    simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,Storage.withCurrent,
      input.enabled,Option.isSome_some,↓reduceIte]
    erw [actual]
    exact configuredWrite
  · unfold BorrowTree.indexOfTag
    change (next.entry.allocation.extra.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
      (Size.ofBytes next.offset) (Size.ofBytes 1) .Write next.tracker.global.protectedTags
      .VisitChildrenOfAccessed).tree.tagMapping.get _ = _
    rw [afterTags]
    exact tagged

end
end DuplicatePrefix.S02SameDestinationUninitInitializedProtection
