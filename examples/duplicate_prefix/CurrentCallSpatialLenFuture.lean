import duplicate_prefix.CurrentCallSpatialDefaultShared
import duplicate_prefix.CurrentCallSpatialLenConstructor
import duplicate_prefix.CurrentCallOptionalSharedOldWindow
import duplicate_prefix.CurrentCallSpatialEntryRead

/-! Mutable-resource associated Read over a fixed spatial cover. The actual
range fold is unchanged; all saved original rows and intersecting cell parent
maps are retained together, independently of interpreter row splitting. -/
namespace DuplicatePrefix.CurrentCallSpatialLenFuture
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallSpatialRows
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowProjection
open GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowExposedConditionalRangeFrames
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

theorem cells {before tracker ctx mode offset length}
    (role : RoleCover before tracker ctx mode offset length)
    (exclusive : demandOf mode=.exclusive)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (short : role.backing.allocation.extra.nodes.size<65536)
    (nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295)
    (parentTag : BorTag) (parent reader : UniIndex) (readerNode : TreeNode)
    (concrete : role.family.value.provenance=.concrete role.backing.id parentTag)
    (tagged : role.backing.allocation.extra.indexOfTag parentTag=some parent)
    (readerAt : role.backing.allocation.extra.nodeAt reader=some readerNode)
    (readerEdge : readerNode.parent=some parent) (hidden : readerNode.isExposed=false)
    (unheld : tracker.global.protectedTags.contains readerNode.tag=false)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount ≠ 0)
    (bounds : start.toNat+amount.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat)
    (readable : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability
      role.backing.allocation.extra location tracker.global.protectedTags reader .Read)) start (start+amount) role.backing.allocation.extra.locations)
    (visit : ChildrenVisitMode) :
    let registered := CurrentCallSpatialEntryRead.registeredTracker role {} room
    let accessed := role.backing.allocation.extra.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes start) (Size.ofBytes amount)
      .Read registered.global.protectedTags visit
    let actual := accessed.tree.newChild (Size.ofBytes start) (.concrete readerNode.tag) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshAnchor.sharedState) .Frozen true
    ∃helper,actual.tree.indexOfTag tracker.global.nextPointerTag=some helper ∧
      ∀(i : Fin role.backing.cells.size) (overlap : CurrentCallSpatialSourceCover.Active role i) (lower upper : UInt64),
        offset≤lower.toNat→upper.toNat≤offset+length→role.backing.cells[i].offset≤lower.toNat→upper.toNat≤role.backing.cells[i].offset+role.backing.cells[i].length→
        ParentInterpretation actual.tree (S05ConcreteProtectedChildCompletion.extend role.backing.cells[i].completion helper reader) ∧
        OwnedOn (S05CompletedAncestryReadMutable.Authority actual.tree (S05ConcreteProtectedChildCompletion.extend role.backing.cells[i].completion helper reader)
          (registered.global.endCall (({} : FrameState).addProtector role.backing.id tracker.global.nextPointerTag)).protectedTags parent)
          lower upper actual.tree.locations := by
  obtain ⟨contract,readRuntime,parents⟩ := CurrentCallSpatialLenAssociatedRead.prepare role exclusive runtime distinct short
    parentTag parent reader readerNode concrete tagged readerAt readerEdge hidden unheld room start amount startEq amountEq nonzero bounds readable visit
  obtain ⟨_,_,_,_,_,helper,helperLookup,_,_⟩ := CurrentCallSpatialLenConstructor.construct role exclusive runtime distinct short nodeRoom
    parentTag parent reader readerNode concrete tagged readerAt readerEdge hidden unheld room start amount startEq amountEq nonzero bounds readable visit
  let registered := CurrentCallSpatialEntryRead.registeredTracker role {} room
  let accessed := role.backing.allocation.extra.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes start) (Size.ofBytes amount)
    .Read registered.global.protectedTags visit
  obtain ⟨_,_,_,_,nodeFresh,mapFresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare role.backing.allocation.extra tracker.global {} role.backing.id room runtime
  have mapped : accessed.tree.indexOfTag readerNode.tag=some reader := by
    change accessed.tree.tagMapping.get readerNode.tag=some reader
    rw [contract.tags]
    exact runtime.formed.allocator.nodeTags reader readerNode readerAt
  have present : accessed.tree.nodeAt reader=some readerNode := by
    change accessed.tree.nodes.get reader=some readerNode
    rw [contract.nodes]
    exact readerAt
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [contract.tags];exact mapFresh
  have nodeFreshAfter : GeneralBorrowProtector.Fresh accessed.tree tracker.global.nextPointerTag := by
    intro row member
    apply nodeFresh row
    rcases row with ⟨index,node⟩
    have atNode:accessed.tree.nodes.get index=some node := (GeneralBorrowFreshReuseProtection.entries_get _ index node).mp (Array.mem_toList_iff.mpr member)
    rw [contract.nodes] at atNode
    exact Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get _ index node).mpr atNode)
  have roomAfter : accessed.tree.nodes.size+1≤4294967295 := by rw [contract.nodes];exact nodeRoom
  have boundAfter : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [contract.capacity];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<registered.global.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have parentOrder : readerNode.tag.value≤tracker.global.nextPointerTag.value :=
    UInt64.le_of_lt (GeneralBorrowParentTagInvariant.parent_below_fresh role.backing.allocation.extra tracker.global runtime reader readerNode readerAt)
  refine ⟨helper,helperLookup,?_⟩
  intro i overlap lower upper requestLower requestUpper cellLower cellUpper
  have owned := CurrentCallSpatialLenAssociatedRead.subwindow role exclusive runtime distinct short parentTag parent reader readerNode
    concrete tagged readerAt readerEdge hidden unheld room start amount startEq amountEq nonzero bounds readable visit i overlap lower upper requestLower requestUpper cellLower cellUpper
  have sourceAt := CurrentCallSpatialRows.source_at role i overlap
  simp only [concrete] at sourceAt
  have grantEq : (role.roles i overlap).grant=parent := by
    have look : CurrentCallSpatialRows.source role=some parent := by simp only [CurrentCallSpatialRows.source,concrete];exact tagged
    exact Option.some.inj (sourceAt.symm.trans look)
  have sourceLive : ∃node,accessed.tree.nodes.get parent=some node := by
    obtain ⟨node,nodeAt,_,_⟩:=(role.roles i overlap).binding
    rw [grantEq] at nodeAt
    exact ⟨node,by rw [contract.nodes];exact nodeAt⟩
  have primaryLive : ∃node,accessed.tree.nodes.get allocationRoot=some node := by
    obtain ⟨node,nodeAt,_⟩:=(role.roles i overlap).issued.capability.rootNode
    exact ⟨node,by rw [contract.nodes];exact nodeAt⟩
  obtain ⟨other,lookup,afterParents,retained⟩ := CurrentCallOptionalSharedOldWindow.future_parents accessed.tree registered.global role.backing.cells[i].completion
    readRuntime (parents i) role.backing.id readerNode.tag tracker.global.nextPointerTag reader readerNode mapped present fresh nodeFreshAfter roomAfter tagBound
    parent sourceLive start amount nonzero boundAfter lower upper (by rw [startEq];exact requestLower) (by rw [startEq,amountEq];exact requestUpper) primaryLive parentOrder owned
  have same : other=helper := Option.some.inj (lookup.symm.trans helperLookup)
  subst other
  exact ⟨afterParents,retained⟩

end
end DuplicatePrefix.CurrentCallSpatialLenFuture
