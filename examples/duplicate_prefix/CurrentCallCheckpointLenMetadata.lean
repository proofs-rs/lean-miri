import duplicate_prefix.CurrentCallCheckpointLen
import duplicate_prefix.CurrentCallSpatialLenFuture
import duplicate_prefix.CurrentCallCheckpointShared
import duplicate_prefix.CurrentCallSpatialLenAssociatedRead
import duplicate_prefix.CurrentCallSpatialEntryRead

/-! Mutable-resource associated Read over a fixed spatial cover. The actual
range fold is unchanged; all saved original rows and intersecting cell parent
maps are retained together, independently of interpreter row splitting. -/
namespace DuplicatePrefix.CurrentCallCheckpointLenMetadata
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallSpatialRows
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowProjection
open GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowExposedConditionalRangeFrames
set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

theorem graph {before tracker ctx mode offset length}
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
    ∃helper node,actual.tree.indexOfTag tracker.global.nextPointerTag=some helper ∧
      actual.tree.nodeAt helper=some node ∧node.tag=tracker.global.nextPointerTag ∧node.parent=some reader ∧node.isExposed=false ∧
      role.backing.allocation.extra.nodes.get helper=none ∧
      (∀index old,role.backing.allocation.extra.nodes.get index=some old→∃changed,
        actual.tree.nodeAt index=some changed ∧changed.tag=old.tag ∧changed.parent=old.parent ∧changed.isExposed=old.isExposed) := by
  obtain ⟨contract,readRuntime,parents⟩ := CurrentCallSpatialLenAssociatedRead.prepare role exclusive runtime distinct short
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
  have roomAfter : accessed.tree.nodes.size+1≤4294967295 := by rw [contract.nodes];exact nodeRoom
  have boundsAfter : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [contract.capacity];exact bounds
  obtain ⟨helper,lookup,⟨node,nodeAt,nodeTag,nodeParent,nodeHidden⟩,old⟩ := GeneralBorrowSharedChildGraph.construct accessed.tree registered.global readRuntime
    readerNode.tag tracker.global.nextPointerTag reader readerNode mapped present fresh roomAfter true start amount nonzero boundsAfter
  have oldFields : ∀index prior,role.backing.allocation.extra.nodes.get index=some prior→∃changed,
      (accessed.tree.newChild (Size.ofBytes start) (.concrete readerNode.tag) tracker.global.nextPointerTag
        (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree.nodeAt index=some changed ∧
      changed.tag=prior.tag ∧changed.parent=prior.parent ∧changed.isExposed=prior.isExposed := by
    intro index prior atPrior
    apply old index prior
    change accessed.tree.nodes.get index=some prior
    rw [contract.nodes]
    exact atPrior
  have vacant : role.backing.allocation.extra.nodes.get helper=none := by
    cases eq : role.backing.allocation.extra.nodes.get helper with
    | none => rfl
    | some prior =>
      obtain ⟨changed,changedAt,changedTag,_,_⟩ := oldFields helper prior eq
      have same : changed=node := Option.some.inj (changedAt.symm.trans nodeAt)
      have priorTag : prior.tag=tracker.global.nextPointerTag := by rw [←changedTag,same,nodeTag]
      have priorMapped:=runtime.formed.allocator.nodeTags helper prior eq
      rw [priorTag] at priorMapped
      have absent : role.backing.allocation.extra.tagMapping.get tracker.global.nextPointerTag=none := by
        simp [UniKeyMap.get,GeneralBorrowTagMap.fresh_find _ _ mapFresh]
      rw [absent] at priorMapped
      contradiction
  exact ⟨helper,node,lookup,nodeAt,nodeTag,nodeParent,nodeHidden,vacant,oldFields⟩

theorem frame {before tracker ctx mode offset length}
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
      S05ConcreteProtectedChildCompletion.LeafFrame accessed.tree actual.tree helper reader ∧
      (∀index old,role.backing.allocation.extra.nodes.get index=some old→∃changed,
        actual.tree.nodes.get index=some changed ∧changed.tag=old.tag ∧changed.parent=old.parent ∧
        changed.isExposed=old.isExposed ∧changed.defaultInitialPermission=old.defaultInitialPermission) := by
  obtain ⟨contract,readRuntime,parents⟩ := CurrentCallSpatialLenAssociatedRead.prepare role exclusive runtime distinct short
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
  have roomAfter : accessed.tree.nodes.size+1≤4294967295 := by rw [contract.nodes];exact nodeRoom
  have boundsAfter : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [contract.capacity];exact bounds
  have futureRuntime := (spatial_install_rule ".CurrentCallOptionalLenFuture.absent_tag_view") accessed.tree registered.global readRuntime role.backing.id tracker.global.nextPointerTag (by
    intro index node atNode
    apply nodeFresh (index,node)
    apply Array.mem_toList_iff.mp
    apply (GeneralBorrowFreshReuseProtection.entries_get _ index node).mpr
    change accessed.tree.nodes.get index=some node at atNode
    rw [contract.nodes] at atNode
    exact atNode)
  let future := registered.global.endCall (({} : FrameState).addProtector role.backing.id tracker.global.nextPointerTag)
  have unheldFuture : future.protectedTags.contains tracker.global.nextPointerTag=false := by
    change (registered.global.protectedTags.remove tracker.global.nextPointerTag).contains tracker.global.nextPointerTag=false
    simp only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none]
  have tagBound : tracker.global.nextPointerTag.value.toNat<future.nextPointerTag.value.toNat := by
    have successor:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  obtain ⟨_,_,_,_,helper,lookup,leaf,oldFields⟩ := CurrentCallSharedConstructorFrame.metadata accessed.tree future futureRuntime
    readerNode.tag tracker.global.nextPointerTag reader readerNode mapped present fresh roomAfter tagBound unheldFuture start amount nonzero boundsAfter
  have same := (spatial_install_rule ".CurrentCallOptionalLenFuture.shared_held_tree") accessed.tree registered.global readRuntime
    readerNode.tag tracker.global.nextPointerTag reader readerNode mapped present fresh roomAfter true false start amount nonzero boundsAfter
  refine ⟨helper,?_,?_,?_⟩
  · rw [same];exact lookup
  · rw [same];exact leaf
  · rw [same]
    intro index old atOld
    apply oldFields index old
    change accessed.tree.nodes.get index=some old
    rw [contract.nodes]
    exact atOld

end
end DuplicatePrefix.CurrentCallCheckpointLenMetadata
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointLenMetadata" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved checkpoint Len metadata dependency {dependency}"
