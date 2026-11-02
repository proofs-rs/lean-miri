import duplicate_prefix.GeneralBorrowFreshRootScopedSharedFnEntry
import duplicate_prefix.GeneralBorrowFreshRootScopedObserverDirectReadRange
import duplicate_prefix.GeneralBorrowObserverSharedConstructor
import duplicate_prefix.GeneralBorrowRawTargetActivity
import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedObserverRawSharedFnEntry
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowPresence GeneralRangeMapOrigins
open GeneralBorrowObserverReadRange (Observer)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Every actual direct child belongs to its parent's normal component, derived
from the runtime forest's reciprocal edge law. -/
private theorem child_supported (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (location : LocationTree) (protections : ProtectedTags) (parent child : UniIndex) (childNode : TreeNode)
    (present : tree.nodeAt child = some childNode) (edge : childNode.parent = some parent)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location protections parent) :
    normal.component.support child.toNat := by
  obtain ⟨forest⟩ := formed.forest location protections
  have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes child childNode present
  have size : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have bounded : child.toNat < (source_normal_projection tree location protections).topology.nodes.size := by rw [size];exact valid
  have projectedEdge : (nodeData (source_normal_projection tree location protections).topology child.toNat).parent = some parent.toNat := by
    change ((source_normal_projection tree location protections).topology.nodes[child.toNat]?.getD ⟨none,[]⟩).parent = _
    rw [projection_topology_node tree location protections child.toNat child childNode rfl present]
    simp only [edge,Option.map_some]
  obtain ⟨parentBound,member⟩ := forest.parentChild child.toNat bounded parent.toNat (by
    simpa only [nodeData,Array.getElem?_eq_getElem bounded,Option.getD_some] using projectedEdge)
  apply normal.component.children parent.toNat normal.component.anchor child.toNat
  change child.toNat ∈ (nodeData (source_normal_projection tree location protections).topology parent.toNat).children
  simpa only [nodeData,Array.getElem?_eq_getElem parentBound,Option.getD_some] using member

/-- The complete actual shared FnEntry borrowing protocol carries the original
mutable observer from BEFORE tag allocation. Fresh Strong registration, the
real shared-parent Read, arbitrary-slot protected Frozen construction and SIFA
are derived. No intermediate/future observer capability is supplied. -/
theorem invoke (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (input : GeneralBorrowFreshRootScopedSharedFnEntry.Input tree global)
    (parentNode observerNode : TreeNode) (observer : UniIndex)
    (parentPresent : tree.nodeAt input.parent = some parentNode) (edge : parentNode.parent = some observer)
    (parentHidden : parentNode.isExposed = false) (parentUnprotected : global.protectedTags.contains parentNode.tag = false)
    (observerPresent : tree.nodeAt observer = some observerNode)
    (observerPath : ((source_normal_projection tree default global.protectedTags).topology.ancestorPath observer.toNat).getLast? = some input.selected.toNat)
    (observerOwned : OwnedOn (Observer tree global.protectedTags observer) input.offset (input.offset+input.len) tree.locations)
    (observerActivity : GeneralBorrowFreshActiveWithin.ActiveWithin tree observer .Write input.offset (input.offset+input.len)) :
    ∃ output, GeneralBorrowRawSharedFnEntry.operation tree global frame allocation input.parentTag input.offset input.len
        .VisitChildrenOfAccessed = .ok output ∧
      output.tag = global.nextPointerTag ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree observer .Write input.offset (input.offset+input.len) ∧
      ∃ child, output.child.tree.indexOfTag output.tag = some child ∧
        Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive output.child.tree output.global.protectedTags
          child input.selected input.maximum input.offset input.len) ∧
        OwnedOn (Observer output.child.tree global.protectedTags observer)
          input.offset (input.offset+input.len) output.child.tree.locations := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowFreshRootScopedRegistration.read_prepare tree global frame allocation input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  obtain ⟨_,_,_,_,nodeFresh,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation input.tagRoom runtime
  let registration := GeneralBorrowFnEntryRegistration.registered global frame allocation input.tagRoom
  have projection (location : LocationTree) : source_normal_projection tree location registration.1.protectedTags =
      source_normal_projection tree location global.protectedTags := by
    change source_normal_projection tree location (global.protectedTags.insert global.nextPointerTag .StrongProtector) = _
    exact GeneralBorrowProtector.normal_projection tree location global.protectedTags global.nextPointerTag .StrongProtector nodeFresh
  have registeredObserver : OwnedOn (Observer tree registration.1.protectedTags observer)
      input.offset (input.offset+input.len) tree.locations := by
    intro position valid positiveWindow start stop
    obtain ⟨old⟩ := observerOwned position valid positiveWindow start stop
    refine ⟨⟨old.component,?_⟩⟩
    intro kind index included bounded
    rw [projection]
    exact old.permissions kind index included bounded
  have parentDifferent : parentNode.tag ≠ global.nextPointerTag := nodeFresh (input.parent,parentNode)
    (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes input.parent parentNode).mpr parentPresent))
  have parentStillUnprotected : registration.1.protectedTags.contains parentNode.tag = false := by
    change (global.protectedTags.insert global.nextPointerTag .StrongProtector).contains parentNode.tag = false
    rw [ProtectorInsertion.contains_other _ _ _ _ parentDifferent]
    exact parentUnprotected
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨done,afterRuntime,⟨afterPositive⟩,afterObserver⟩ := GeneralBorrowFreshRootScopedObserverDirectReadRange.access tree registration.1 registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged parentNode parentPresent observer observerNode
    edge observerPresent parentHidden parentStillUnprotected observerPath (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len registeredPositive registeredObserver input.distinct input.short
    (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨contract,_,_⟩ := GeneralBorrowFreshRootScopedReadRange.access tree registration.1 registeredRuntime input.parentTag input.parent
    input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed
    input.offset input.len registeredPositive input.distinct input.short (Nat.le_refl _) (Nat.le_refl _)
  have parentAfter : accessed.tree.nodeAt input.parent = some parentNode := by
    change accessed.tree.nodes.get input.parent = some parentNode
    rw [contract.nodes]
    exact parentPresent
  have observerAfter : accessed.tree.nodeAt observer = some observerNode := by
    change accessed.tree.nodes.get observer = some observerNode
    rw [contract.nodes]
    exact observerPresent
  have edgeAfter : parentNode.parent = some observer := edge
  have nodeFreshAfter : GeneralBorrowProtector.Fresh accessed.tree global.nextPointerTag := by
    change ∀ row ∈ accessed.tree.nodes.entries, row.2.tag ≠ global.nextPointerTag
    rw [contract.nodes]
    exact nodeFresh
  have projectionAfter (location : LocationTree) : source_normal_projection accessed.tree location registration.1.protectedTags =
      source_normal_projection accessed.tree location global.protectedTags := by
    change source_normal_projection accessed.tree location (global.protectedTags.insert global.nextPointerTag .StrongProtector) = _
    exact GeneralBorrowProtector.normal_projection accessed.tree location global.protectedTags global.nextPointerTag .StrongProtector nodeFreshAfter
  have constructorObserver : OwnedOn (fun location => ∃ normal : DuplicatePrefixBorrowAuthorization.Normal accessed.tree location global.protectedTags observer,
      normal.component.support input.parent.toNat) input.offset (input.offset+input.len) accessed.tree.locations := by
    intro position valid positiveWindow start stop
    obtain ⟨old⟩ := afterObserver position valid positiveWindow start stop
    let normal : DuplicatePrefixBorrowAuthorization.Normal accessed.tree accessed.tree.locations.entries[position].data global.protectedTags observer := {
      component := old.component
      permissions := by
        intro kind index included bounded
        rw [←projectionAfter]
        exact old.permissions kind index included bounded }
    exact ⟨normal,child_supported accessed.tree afterRuntime.formed.toGraphState _ global.protectedTags observer input.parent parentNode parentAfter edgeAfter normal⟩
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have bound : global.nextPointerTag.value.toNat < registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag input.tagRoom
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag input.tagRoom).value.toNat
    omega
  have heldTag : registration.1.protectedTags.contains global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  have complete := GeneralBorrowForestTagHighWater.complete tree _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨_,_,unheld⟩ := GenericFunctionTagFormation.fresh_above tree _ _ global.nextPointerTag complete (Nat.le_refl _)
  have nonzero : input.len ≠ 0 := by intro zero;have p:=input.positive.base.positive;rw [zero] at p;contradiction
  obtain ⟨_,_,_,_,observerChild,observerLookup,observerRows⟩ := GeneralBorrowObserverSharedConstructor.construct accessed.tree registration.1 afterRuntime
    input.parentTag global.nextPointerTag input.parent parentNode tagged parentAfter freshAfter room bound true heldTag
    observer observerNode observerAfter global.protectedTags unheld input.offset input.len nonzero afterPositive.base.bounds constructorObserver
  have readActivity : GeneralBorrowFreshActiveWithin.ActiveWithin accessed.tree observer .Write input.offset (input.offset+input.len) :=
    GeneralBorrowFreshActiveWithinAccess.normal tree input.parentTag (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read
      registration.1.protectedTags .VisitChildrenOfAccessed observer input.offset (input.offset+input.len)
      runtime.formed.well input.positive.base.bounds (Nat.le_refl _) (Nat.le_refl _) observerActivity
  have childObserverActivity := GeneralBorrowRawTargetActivity.shared accessed.tree registration.1 afterRuntime
    input.parentTag global.nextPointerTag input.parent parentNode tagged parentAfter freshAfter room true
    input.offset input.len nonzero afterPositive.base.bounds observer input.offset (input.offset+input.len)
    (Nat.le_refl _) (Nat.le_refl _) readActivity
  obtain ⟨output,operation,tagEq,globalEq,_,_,accessDone,childDone,childRuntime,_,_,child,lookup,_,_,childPositive,_⟩ :=
    GeneralBorrowFreshRootScopedSharedFnEntry.invoke tree global frame allocation runtime input
  let computed : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen true⟩
  have computedOperation : GeneralBorrowRawSharedFnEntry.operation tree global frame allocation input.parentTag input.offset input.len
      .VisitChildrenOfAccessed = .ok computed := by
    simp only [GeneralBorrowRawSharedFnEntry.operation,allocated,Except.bind,Except.pure,bind,pure]
    rfl
  have same : output = computed := Except.ok.inj (operation.symm.trans computedOperation)
  subst output
  refine ⟨computed,computedOperation,rfl,accessDone,childDone,childRuntime,childObserverActivity,child,lookup,childPositive,?_⟩
  intro position valid positiveWindow start stop
  obtain ⟨normal,_,_⟩ := observerRows position valid positiveWindow start stop
  exact ⟨normal⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedObserverRawSharedFnEntry
