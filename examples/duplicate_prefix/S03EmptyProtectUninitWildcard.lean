import duplicate_prefix.S03EmptyWildcardRetagFacts
import duplicate_prefix.S04ReturnReleaseParent

namespace DuplicatePrefix.S03EmptyProtectUninitWildcard
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
open TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
noncomputable section

private theorem hidden_tag (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some index) (present : tree.nodeAt index = some node)
    (hidden : node.isExposed = false) :
    ∀ query value,tree.nodeAt query = some value → value.tag = tag → value.isExposed = false := by
  intro query value found sameTag
  have mapped := runtime.formed.allocator.nodeTags query value found
  rw [sameTag] at mapped
  have equal : query = index := Option.some.inj (mapped.symm.trans tagged)
  subst query
  have nodes := Option.some.inj (found.symm.trans present)
  exact nodes ▸ hidden

/-- Actual wildcard return protection and uninitializing Write retain the
original empty argument tag's Data/Quiescent packet and exact caller protectors.
The return root, runtime and physical metadata are all generated internally. -/
theorem invoke
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat) (before : Before) (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (wildcard : input.pointer.provenance = .wildcard)
    (zeroTag : BorTag) (zeroIndex : UniIndex) (zero : S03EmptyTagState.Data input.entry.allocation.extra zeroTag zeroIndex)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (owned : borrowFrame.protectedTags = #[(input.id,zeroTag)])
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync,
      row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat+1 ≤ row.1.bytes.toNat) :
    ∃ tree updated,
      let global := registeredGlobal (allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag
      let written := (tree.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
        (Size.ofBytes input.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
      (TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag budget place
        (Storage.withCurrent frames frame before) =
        .ok () (S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated) ∧
      updated.extra = written ∧ updated.byteSize = input.entry.allocation.byteSize ∧
      updated.len = input.entry.allocation.len ∧ updated.mutability = .Mut ∧
      InitMaskCopy.WellFormed updated.initializationMask ∧
      updated.initializationMask.len = input.entry.allocation.initializationMask.len ∧
      (∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len) ∧
      written.locations.size = input.entry.allocation.extra.locations.size ∧
      DuplicatePrefixBorrowContract.RuntimeFacts written global ∧
      written.nodes.size < 65536 ∧ written.roots.toList.Nodup ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder written ∧
      GeneralBorrowFreshRootSupportCutoff.ExposedBound written input.tracker.global.nextPointerTag ∧
      ∃ child, written.indexOfTag input.tracker.global.nextPointerTag = some child ∧
        written.roots = input.entry.allocation.extra.roots.push child ∧
        Nonempty (GeneralBorrowFreshRootScopedRow.Positive written global.protectedTags
          child child input.tracker.global.nextPointerTag input.offset 1) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin written child .Write input.offset (input.offset+1) ∧
        ∃ node, written.nodeAt child = some node ∧ node.tag = input.tracker.global.nextPointerTag ∧
          node.parent = none ∧ node.children = #[] ∧ node.isExposed = false) ∧
      Nonempty (S03EmptyTagState.Data written zeroTag zeroIndex) ∧
      S04ReturnReleaseInactive.Quiescent written zeroIndex ∧
      (borrowFrame.addProtector input.id input.tracker.global.nextPointerTag).protectedTags =
        #[(input.id,zeroTag),(input.id,input.tracker.global.nextPointerTag)] ∧
      S04ReturnReleaseParent.HiddenFrame written (borrowFrame.addProtector input.id input.tracker.global.nextPointerTag) := by
  obtain ⟨tree,⟨actual,post,capacity,short,rootsDistinct,treeOrder,treeExposed,child,tagged,roots,⟨positive⟩,active,geometry⟩,⟨retagZero⟩⟩ :=
    S03EmptyWildcardRetagFacts.retag budget before model place input runtime distinct order headroom fresh wildcard zeroTag zeroIndex zero
      frames frame borrowFrame frameBorrow
  let global := registeredGlobal (allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag
  let current := ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree
  let next := S04ReturnRetaggedInput.from_borrowed input frames frame borrowFrame fresh tree child (some child)
    (some input.tracker.global.nextPointerTag) tagged capacity positive.base
  obtain ⟨updated,write,extra,bytes,length,mutable,maskWf,maskLen,pointerBounds,afterRuntime,afterTags,afterPositive,afterActive⟩ :=
    S04ProtectUninitScopedWrite.from_current (options := options) (remaining := remaining) span current _ next post rootsDistinct
      short input.tracker.global.nextPointerTag child tagged positive rfl model.noDataRace model.noBackend sync extras outside
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
  let written := (tree.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
  have tagFresh := GeneralBorrowParentTagInvariant.fresh input.entry.allocation.extra input.tracker.global runtime
  have tagDifferent := S03EmptyReturnConstructorFacts.fresh_ne input.entry.allocation.extra input.tracker.global.nextPointerTag
    zeroTag zeroIndex tagFresh zero.tagged
  have different : zeroIndex ≠ child := by
    intro equal
    obtain ⟨node,found,sameTag,parentless,leaf,hidden⟩ := geometry
    rw [←equal] at found
    have nodes := Option.some.inj (found.symm.trans retagZero.present)
    have tags := congrArg TreeNode.tag nodes
    rw [sameTag,retagZero.sameTag] at tags
    exact tagDifferent tags
  let afterWriteZero := S03EmptyTagState.access tree global post zeroTag input.tracker.global.nextPointerTag zeroIndex child child
    (some input.tracker.global.nextPointerTag) retagZero different input.offset 1 positive.base tagged .Write .VisitChildrenOfAccessed
  have framed : written.nodes = tree.nodes ∧ written.roots = tree.roots ∧ written.locations.size = tree.locations.size := by
    obtain ⟨contract,_,_⟩ := GeneralBorrowFreshRootScopedRange.access_runtime_kind tree global post
      input.tracker.global.nextPointerTag child child input.tracker.global.nextPointerTag tagged
      (Size.ofBytes input.offset) (Size.ofBytes 1) .Write .VisitChildrenOfAccessed input.offset 1 positive rootsDistinct short
      (Nat.le_refl _) (Nat.le_refl _)
    exact ⟨contract.nodes,contract.roots,contract.capacity⟩
  have writtenOrder := GeneralBorrowParentTagInvariant.nodes_frame tree written framed.1 treeOrder
  have writtenExposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound written input.tracker.global.nextPointerTag := by
    intro index value found exposed
    change written.nodes.get index = some value at found
    rw [framed.1] at found
    exact treeExposed index value found exposed
  have writtenTagged : written.indexOfTag input.tracker.global.nextPointerTag = some child := by
    unfold BorrowTree.indexOfTag
    change (next.entry.allocation.extra.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
      (Size.ofBytes next.offset) (Size.ofBytes 1) .Write next.tracker.global.protectedTags
      .VisitChildrenOfAccessed).tree.tagMapping.get _ = _
    rw [afterTags]
    exact tagged
  have writtenRoot : ∃ node,written.nodeAt child = some node ∧ node.tag = input.tracker.global.nextPointerTag ∧
      node.parent = none ∧ node.children = #[] ∧ node.isExposed = false := by
    obtain ⟨node,present,same,parentless,leaf,hidden⟩ := geometry
    exact ⟨node,by change written.nodes.get child = _;rw [framed.1];exact present,same,parentless,leaf,hidden⟩
  have protectedOwned : (borrowFrame.addProtector input.id input.tracker.global.nextPointerTag).protectedTags =
      #[(input.id,zeroTag),(input.id,input.tracker.global.nextPointerTag)] := by
    simp only [FrameState.addProtector,owned]
    rfl
  refine ⟨tree,updated,⟨?_,extra,bytes,length,mutable,maskWf,maskLen,pointerBounds,framed.2.2.trans capacity,afterRuntime,
    ?_,?_,writtenOrder,writtenExposed,child,writtenTagged,?_,afterPositive,afterActive child active,writtenRoot⟩,
    ⟨afterWriteZero⟩,?_,protectedOwned,?_⟩
  · unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
    simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,Storage.withCurrent,
      input.enabled,Option.isSome_some,↓reduceIte]
    erw [actual]
    exact configuredWrite
  · rw [framed.1]
    exact short
  · rw [framed.2.1]
    exact rootsDistinct
  · rw [framed.2.1]
    exact roots
  · intro position valid state stored
    exact Or.inl (afterWriteZero.inactive position valid state stored)
  · obtain ⟨node,found,same,parentless,leaf,hidden⟩ := writtenRoot
    have zeroHidden := hidden_tag written global afterRuntime zeroTag zeroIndex afterWriteZero.node afterWriteZero.tagged
      afterWriteZero.present afterWriteZero.hidden
    have returnHidden := hidden_tag written global afterRuntime input.tracker.global.nextPointerTag child node writtenTagged found hidden
    intro row member index value present sameTag
    rw [protectedOwned] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with equal | equal
    · subst row
      exact zeroHidden index value present sameTag
    · subst row
      exact returnHidden index value present sameTag

end
end DuplicatePrefix.S03EmptyProtectUninitWildcard
