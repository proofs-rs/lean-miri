import duplicate_prefix.GeneralBorrowRawSharedToLenLiteralLedger
namespace DuplicatePrefix.S02SameDestinationRejectedResultOrder
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section
theorem expression (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawShared.Input tree tracker.global)
    (oldOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree) :
    let finalTree := (GeneralBorrowRawSharedExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder finalTree := by
  obtain ⟨allocated,registeredRuntime,⟨registeredPositive⟩,fresh,unheld⟩ :=
    GeneralBorrowReadTagAllocation.prepare tree tracker.global input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.advanced tracker.global input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowReadRowRange.access tree registration registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.order input.short
    (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.sourcePresent
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by intro zero;have p := input.positive.positive;rw [zero] at p;contradiction
  have accessedNodes : accessed.tree.nodes = tree.nodes := contract.nodes
  have accessedOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder accessed.tree := by
    simpa only [GeneralBorrowWildcardParentTagOrder.ParentTagOrder,accessedNodes] using oldOrder
  have originalParent : tree.nodeAt input.parent = some parentNode := by
    change tree.nodes.get input.parent = some parentNode
    change accessed.tree.nodes.get input.parent = some parentNode at parentPresent
    simpa only [accessedNodes] using parentPresent
  have mapped := runtime.formed.allocator.nodeTags input.parent parentNode originalParent
  have below := GeneralBorrowForestTagHighWater.mapped tree tracker.global.protectedTags tracker.global.nextPointerTag parentNode.tag
    runtime.below input.parent mapped
  have parentOrder : parentNode.tag.value ≤ tracker.global.nextPointerTag.value := UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt below)
  exact GeneralBorrowSharedChildParentTagOrder.construct accessed.tree registration afterRuntime
    input.parentTag tracker.global.nextPointerTag input.parent parentNode tagged parentPresent freshAfter room
    false input.offset input.len nonzero afterPositive.bounds accessedOrder parentOrder
theorem helper (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawSharedFnEntry.Input tree tracker.global)
    (oldOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree) :
    let finalTree := GeneralBorrowRawSharedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder finalTree := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowFnEntryReadRegistration.prepare tree tracker.global frame allocation input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global frame allocation input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowReadRowRange.access tree registration.1 registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.order input.short
    (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.sourcePresent
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have nonzero : input.len ≠ 0 := by intro zero;have p := input.positive.positive;rw [zero] at p;contradiction
  have accessedNodes : accessed.tree.nodes = tree.nodes := contract.nodes
  have accessedOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder accessed.tree := by
    simpa only [GeneralBorrowWildcardParentTagOrder.ParentTagOrder,accessedNodes] using oldOrder
  have originalParent : tree.nodeAt input.parent = some parentNode := by
    change tree.nodes.get input.parent = some parentNode
    change accessed.tree.nodes.get input.parent = some parentNode at parentPresent
    simpa only [accessedNodes] using parentPresent
  have mapped := runtime.formed.allocator.nodeTags input.parent parentNode originalParent
  have below := GeneralBorrowForestTagHighWater.mapped tree tracker.global.protectedTags tracker.global.nextPointerTag parentNode.tag
    runtime.below input.parent mapped
  have parentOrder : parentNode.tag.value ≤ tracker.global.nextPointerTag.value := UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt below)
  exact GeneralBorrowSharedChildParentTagOrder.construct accessed.tree registration.1 afterRuntime
    input.parentTag tracker.global.nextPointerTag input.parent parentNode tagged parentPresent freshAfter room
    true input.offset input.len nonzero afterPositive.bounds accessedOrder parentOrder

theorem literal (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawShared.Input tree tracker.global)
    (shortRoom : tree.nodes.size+2 < 65536) (nodeRoom : tree.nodes.size+2 ≤ 4294967295)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (ordered : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree) :
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder
      (GeneralBorrowRawSharedToLenLiteralLedger.finalTree tree tracker input.parentTag input.offset input.len input.tagRoom) := by
  let expr := (GeneralBorrowRawSharedExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag
    input.offset input.len .VisitChildrenOfAccessed).tree
  let next := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
  have first := expression tree tracker runtime input ordered
  obtain ⟨exprRuntime,capacity,raw,tag,_selected,_maximum,offset,len⟩ :=
    GeneralBorrowRawSharedNext.next_input tree tracker runtime input (by omega) nodeRoom tagRoom
  have second := helper expr next {} allocation exprRuntime raw first
  have released := GeneralBorrowStructuralReleaseGeometryFrame.release
    (GeneralBorrowRawSharedFnEntryArgument.finalTree expr next raw.parentTag raw.offset raw.len)
    (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker next raw.tagRoom) next.global.nextPointerTag).global.protectedTags
    next.global.nextPointerTag
  have finalOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder
      (GeneralBorrowSharedLenHelperGraph.releasedTree expr next raw) := by
    have frame := (congrArg BorrowTree.nodes (GeneralBorrowSharedLenHelperGraph.releasedTree_eq expr next raw)).trans
      (congrArg BorrowTree.nodes released)
    unfold GeneralBorrowWildcardParentTagOrder.ParentTagOrder at *
    rw [frame]
    exact second
  rw [GeneralBorrowSharedLenHelperGraph.releasedTree_eq] at finalOrder
  simp only [tag,offset,len] at finalOrder
  exact finalOrder
end
end DuplicatePrefix.S02SameDestinationRejectedResultOrder
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationRejectedResultOrder.literal) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved full order transport dependency {dependency}"
