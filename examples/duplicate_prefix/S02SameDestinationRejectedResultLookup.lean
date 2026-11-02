import duplicate_prefix.GeneralBorrowRawSharedToLenLiteralLedger
namespace DuplicatePrefix.S02SameDestinationRejectedResultLookup
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshAnchor
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (held : Bool) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (oldTag : BorTag) (query : UniIndex) (old : tree.indexOfTag oldTag = some query) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) sharedState) .Frozen held
    actual.tree.indexOfTag oldTag = some query := by
  have different : newTag ≠ oldTag := by
    intro same
    have absent := GeneralBorrowTagMap.fresh_find tree.tagMapping newTag fresh
    change tree.tagMapping.get oldTag = some query at old
    unfold UniKeyMap.get at old
    rw [←same,absent] at old
    cases old
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    exact ((GeneralBorrowFreshMetadataChildShared.append input).oldLookup oldTag different).trans old
  | reuse child available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,valid,vacant,slack,held,offset,len,nonzero,runtime.formed.well,bounds⟩
    exact ((GeneralBorrowFreshMetadataChildSharedReuse.reuse input).oldLookup oldTag different).trans old
theorem expression (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawShared.Input tree tracker.global)
    (oldTag : BorTag) (query : UniIndex) (old : tree.indexOfTag oldTag = some query) :
    let finalTree := (GeneralBorrowRawSharedExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag input.offset input.len .VisitChildrenOfAccessed).tree
    finalTree.indexOfTag oldTag = some query := by
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
  have oldRead : accessed.tree.indexOfTag oldTag = some query := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]; exact old
  exact construct accessed.tree registration afterRuntime input.parentTag tracker.global.nextPointerTag input.parent
    parentNode tagged parentPresent freshAfter room false input.offset input.len nonzero afterPositive.bounds oldTag query oldRead
theorem helper (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawSharedFnEntry.Input tree tracker.global)
    (oldTag : BorTag) (query : UniIndex) (old : tree.indexOfTag oldTag = some query) :
    let finalTree := GeneralBorrowRawSharedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    finalTree.indexOfTag oldTag = some query := by
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
  have oldRead : accessed.tree.indexOfTag oldTag = some query := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]; exact old
  exact construct accessed.tree registration.1 afterRuntime input.parentTag tracker.global.nextPointerTag input.parent
    parentNode tagged parentPresent freshAfter room true input.offset input.len nonzero afterPositive.bounds oldTag query oldRead

theorem literal (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawShared.Input tree tracker.global)
    (shortRoom : tree.nodes.size+2 < 65536) (nodeRoom : tree.nodes.size+2 ≤ 4294967295)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (oldTag : BorTag) (query : UniIndex) (old : tree.indexOfTag oldTag = some query) :
    (GeneralBorrowRawSharedToLenLiteralLedger.finalTree tree tracker input.parentTag input.offset input.len input.tagRoom).indexOfTag oldTag = some query := by
  let expr := (GeneralBorrowRawSharedExpression.child tree tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag
    input.offset input.len .VisitChildrenOfAccessed).tree
  let next := ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom
  have first := expression tree tracker runtime input oldTag query old
  obtain ⟨exprRuntime,capacity,raw,tag,_selected,_maximum,offset,len⟩ :=
    GeneralBorrowRawSharedNext.next_input tree tracker runtime input (by omega) nodeRoom tagRoom
  have second := helper expr next {} allocation exprRuntime raw oldTag query first
  have released := GeneralBorrowStructuralReleaseGeometryFrame.release
    (GeneralBorrowRawSharedFnEntryArgument.finalTree expr next raw.parentTag raw.offset raw.len)
    (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker next raw.tagRoom) next.global.nextPointerTag).global.protectedTags
    next.global.nextPointerTag
  have finalLookup : (GeneralBorrowSharedLenHelperGraph.releasedTree expr next raw).indexOfTag oldTag = some query := by
    have frame := (congrArg BorrowTree.tagMapping (GeneralBorrowSharedLenHelperGraph.releasedTree_eq expr next raw)).trans
      (congrArg BorrowTree.tagMapping released)
    unfold BorrowTree.indexOfTag
    rw [frame]
    exact second
  rw [GeneralBorrowSharedLenHelperGraph.releasedTree_eq] at finalLookup
  simp only [tag,offset,len] at finalLookup
  exact finalLookup
end
end DuplicatePrefix.S02SameDestinationRejectedResultLookup
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationRejectedResultLookup.literal) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved old lookup transport dependency {dependency}"
