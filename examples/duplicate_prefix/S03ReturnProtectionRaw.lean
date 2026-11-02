import duplicate_prefix.S04ProtectUninit

namespace DuplicatePrefix.S03ReturnProtectionRaw
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Current local resources for one return-child insertion, without asking
for the original sixteen-slot call budget again after argument initialization. -/
theorem packet {before : Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag) :
    ∃ raw : GeneralBorrowRawFnEntry.Input input.entry.allocation.extra input.tracker.global,
      raw.parentTag = tag ∧ raw.offset = input.offset ∧ raw.len = 1 ∧
      input.selectedRoot = some raw.selected ∧ raw.maximum = input.maximum := by
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
  obtain ⟨_,parent,source,tagged⟩ := binding
  have positive := input.borrow
  rw [source] at positive
  obtain ⟨selected,selectedEq⟩ := S05ConcreteEntryBridge.selected_root _ _ parent input.selectedRoot
    input.maximum input.offset 1 runtime.formed positive
  rw [selectedEq] at positive
  let raw : GeneralBorrowRawFnEntry.Input input.entry.allocation.extra input.tracker.global := {
    parentTag := tag, parent := parent, selected := selected, maximum := input.maximum,
    offset := input.offset, len := 1, tagged := tagged, positive := positive,
    distinct := distinct, order := fun _ _ => order, short := by omega,
    nodeRoom := by omega, tagRoom := fresh }
  exact ⟨raw,rfl,rfl,rfl,selectedEq,rfl⟩

/-- The actual configured protection retag on the canonical raw FnEntry tree.
Only one tag/node margin is consumed; every post-state fact is derived. -/
theorem retag
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
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame) :
    let tree := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker input.tracker fresh)
      input.tracker.global.nextPointerTag
    TypedRetag.retagPlace (config options remaining span).retag budget place MachineHooks.protectionPolicy
      (Storage.withCurrent frames frame before) =
      .ok (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag)
        (ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts tree global ∧
    tree.locations.size = input.entry.allocation.extra.locations.size ∧
    tree.nodes.size < 65536 ∧ tree.roots.toList.Nodup ∧
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree ∧
    ∃ child, tree.indexOfTag input.tracker.global.nextPointerTag = some child ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags
        (some child) input.selectedRoot input.maximum input.offset 1) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin tree child .Write input.offset (input.offset+1) := by
  obtain ⟨raw,parentTag,offset,length,selected,maximum⟩ := packet input runtime distinct order headroom fresh tag concrete
  have completed := GeneralBorrowRawFnEntryExecution.completed input.entry.allocation.extra input.tracker.global
    borrowFrame input.id runtime raw
  obtain ⟨ctx⟩ := ActualRetagContext.exists_context options remaining span model.preciseOff model.implicitOff
  let tree := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1
  have pointer : place.mplace.ptr = Pointer.new (some (.concrete input.id tag)) (Size.ofBytes (input.base+input.offset)) := by
    rw [input.physicalPointer]
    have off : input.pointer.offset = Size.ofBytes (input.base+input.offset) := by
      cases h : input.pointer.offset
      simpa [h,Size.ofBytes] using congrArg Size.ofBytes input.pointerAddress
    simp only [Pointer.withOptionalProvenance,concrete,off,Pointer.new]
  have actual := S04ReturnProtection.retag_bool_window_from_tree options remaining span ctx budget place input.layout
    frames frame borrowFrame before input.tracker input.enabled frameBorrow fresh input.id input.entry input.base input.offset
    tag pointer input.cachedBase (by simpa only [input.size,Size.ofBytes] using input.bounds) input.live model.noDataRace
    _ tree rfl
    (by simpa only [parentTag,offset,length,TypedBorrowSteps.registeredGlobal,
      ReferenceBorrowDriver.allocatedTracker] using completed.1)
    (by
      have record := S04ReturnProtection.child_record _ completed.2
      simpa only [tree,GeneralBorrowRawFnEntryArgument.finalTree,parentTag,offset,length,
        GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome,
        TypedBorrowSteps.registeredGlobal,ReferenceBorrowDriver.allocatedTracker] using record)
  obtain ⟨post,capacity,growth,roots,_,_,_,child,tagged,positive,activity⟩ :=
    GeneralBorrowRawFnEntryResources.resources input.entry.allocation.extra input.tracker borrowFrame input.id runtime raw
  have postOrder := GeneralBorrowRawFnEntryOrder.order input.entry.allocation.extra input.tracker borrowFrame input.id
    runtime raw order
  simp only [parentTag,offset,length] at post capacity growth roots tagged positive activity postOrder
  refine ⟨actual,post,capacity,by omega,?_,postOrder,child,tagged,?_,activity⟩
  · rw [roots]
    exact distinct
  · simpa only [selected,maximum] using positive

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
      updated.extra = written ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      DuplicatePrefixBorrowContract.RuntimeFacts written global ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder written ∧
      ∃ child, written.indexOfTag input.tracker.global.nextPointerTag = some child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive written global.protectedTags
          (some child) input.selectedRoot input.maximum input.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin written child .Write input.offset (input.offset+1) := by
  obtain ⟨actual,post,capacity,short,roots,postOrder,child,tagged,⟨positive⟩,active⟩ :=
    retag budget before model place input runtime distinct order headroom fresh tag concrete frames frame borrowFrame frameBorrow
  let tree := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1
  let current := ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree
  let next := S04ReturnRetaggedInput.from_borrowed input frames frame borrowFrame fresh tree child input.selectedRoot
    input.maximum tagged capacity positive
  obtain ⟨updated,write,extra,bytes,length,mutable,afterRuntime,afterTags,afterOrder,afterPositive,afterActive⟩ :=
    S04ProtectUninitWrite.from_current (options := options) (remaining := remaining) span current _ next post roots postOrder
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
  refine ⟨updated,?_,extra,bytes,length,mutable,afterRuntime,afterOrder,child,?_,afterPositive,afterActive child active⟩
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
end DuplicatePrefix.S03ReturnProtectionRaw
