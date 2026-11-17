import duplicate_prefix.CurrentCallSpatialDefaultShared
import duplicate_prefix.CurrentCallSpatialLenAssociatedRead
import duplicate_prefix.CurrentCallSpatialEntryRead

/-! Mutable-resource associated Read over a fixed spatial cover. The actual
range fold is unchanged; all saved original rows and intersecting cell parent
maps are retained together, independently of interpreter row splitting. -/
namespace DuplicatePrefix.CurrentCallSpatialLenConstructor
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

theorem construct {before tracker ctx mode offset length}
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
    accessed.status=.Completed ∧actual.outcome=.ok () ∧DuplicatePrefixBorrowContract.RuntimeFacts actual.tree registered.global ∧
    actual.tree.locations.size=role.backing.allocation.extra.locations.size ∧actual.tree.nodes.size≤role.backing.allocation.extra.nodes.size+1 ∧
    ∃helper,actual.tree.indexOfTag tracker.global.nextPointerTag=some helper ∧
      OwnedOn (GeneralBorrowSharedReadConstructor.Capabilities actual.tree registered.global.protectedTags reader helper)
        start (start+amount) actual.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree helper .Read start (start+amount) := by
  obtain ⟨contract,readRuntime,parents⟩ := CurrentCallSpatialLenAssociatedRead.prepare role exclusive runtime distinct short
    parentTag parent reader readerNode concrete tagged readerAt readerEdge hidden unheld room start amount startEq amountEq nonzero bounds readable visit
  let registered := CurrentCallSpatialEntryRead.registeredTracker role {} room
  let accessed := role.backing.allocation.extra.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes start) (Size.ofBytes amount)
    .Read registered.global.protectedTags visit
  obtain ⟨_,tagHeld,_,_,_,mapFresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare role.backing.allocation.extra tracker.global {} role.backing.id room runtime
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
  have boundAfter : start.toNat+amount.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [contract.capacity];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<registered.global.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have aligned : registered.global.protectedTags.contains tracker.global.nextPointerTag=true := by
    unfold ProtectedTags.contains
    change ((GeneralBorrowFnEntryRegistration.registered tracker.global {} role.backing.id room).1.protectedTags.get tracker.global.nextPointerTag).isSome=true
    rw [tagHeld];rfl
  have cap : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability accessed.tree location registered.global.protectedTags reader .Read))
      start (start+amount) accessed.tree.locations := by
    rw [contract.tree_eq]
    intro cursor valid positive beforeUpper afterLower
    obtain ⟨capability⟩ := contract.rows cursor valid positive beforeUpper afterLower
    exact ⟨⟨capability.component,capability.permissions⟩⟩
  have output := GeneralBorrowSharedReadConstructor.construct accessed.tree registered.global readRuntime readerNode.tag tracker.global.nextPointerTag
    reader readerNode mapped present fresh roomAfter tagBound true aligned start amount nonzero boundAfter cap
  obtain ⟨helper,lookup,both⟩ := output.2.2.2.2
  obtain ⟨_,other,otherLookup,activity⟩ := S05SharedChildActivity.construct accessed.tree registered.global readRuntime readerNode.tag tracker.global.nextPointerTag
    reader readerNode mapped present fresh roomAfter tagBound true aligned start amount nonzero boundAfter
  have same : other=helper := Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  refine ⟨contract.completed,output.1,output.2.1,output.2.2.1.trans contract.capacity,?_,helper,lookup,both,activity⟩
  calc _≤accessed.tree.nodes.size+1 := output.2.2.2.1
       _=role.backing.allocation.extra.nodes.size+1 := by rw [contract.nodes]

end
end DuplicatePrefix.CurrentCallSpatialLenConstructor
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialLenConstructor" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial Len dependency {dependency}"
