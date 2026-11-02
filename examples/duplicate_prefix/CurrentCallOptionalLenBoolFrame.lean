import duplicate_prefix.CurrentCallOptionalLenAssociatedRead
import duplicate_prefix.CurrentCallSharedConstructorFrame
import duplicate_prefix.S05SharedConstructorDisjoint
import duplicate_prefix.CurrentCallReadRootActivity
import duplicate_prefix.GeneralBorrowSharedReadConstructor
import duplicate_prefix.S05SharedChildActivity
import duplicate_prefix.S02DisjointReleaseFrame
import duplicate_prefix.GeneralBorrowRangeOutsideOwned

namespace DuplicatePrefix.CurrentCallOptionalLenBoolFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowProjection GeneralRangeMapOrigins
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
open S05ConcreteProtectedChildCompletion OrdinaryBorrowAuthority
open S05CompletedAncestryReadMutable (Authority)
open CurrentCallResourceNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The actual Strong shared helper sequence retains the current Bool child's
full disjoint authority and its hidden-leaf activity. The release may stop at
any actual failure prefix; no successful-release premise is needed. -/
theorem construct (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : ParentInterpretation tree completion)
    (primarySlot : tree.roots[0]? = some allocationRoot) (distinct : tree.roots.toList.Nodup)
    (order : ParentTagOrder tree)
    (position : Nat) (root source reader target : UniIndex) (rootNode readerNode targetNode : TreeNode)
    (primaryBelow : Below completion allocationRoot source)
    (rootSlot : tree.roots[position]? = some root) (rootAt : tree.nodes.get root = some rootNode)
    (sourcePath : Path tree root source) (readerAt : tree.nodeAt reader = some readerNode)
    (readerPath : Path tree root reader) (readerEdge : readerNode.parent = some source)
    (hidden : readerNode.isExposed = false) (readerUnheld : global.protectedTags.contains readerNode.tag = false)
    (targetAt : tree.nodeAt target = some targetNode) (targetLeaf : targetNode.children = #[])
    (targetHidden : targetNode.isExposed = false) (different : target ≠ reader)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (offset len lower upper : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size+1 < 65536)
    (disjoint : (offset+len).toNat ≤ lower.toNat ∨ upper.toNat ≤ offset.toNat)
    (readable : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read))
      offset (offset+len) tree.locations)
    (owned : OwnedOn (Authority tree completion global.protectedTags source) offset (offset+len) tree.locations)
    (targetOwned : OwnedOn (Authority tree completion global.protectedTags target) lower upper tree.locations)
    (targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower upper) :
    let registration := GeneralBorrowFnEntryRegistration.registered global {} allocation room
    let accessed := tree.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes offset) (Size.ofBytes len)
      .Read registration.1.protectedTags .VisitChildrenOfAccessed
    let child := accessed.tree.newChild (Size.ofBytes offset) (.concrete readerNode.tag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true
    let released := child.tree.releaseProtector global.nextPointerTag registration.1.protectedTags
    ∃ helper, child.tree.indexOfTag global.nextPointerTag = some helper ∧
      OwnedOn (Authority released.tree (extend completion helper reader)
        (registration.1.endCall registration.2).protectedTags target) lower upper released.tree.locations ∧
      (∃ next, released.tree.nodeAt target = some next ∧ next.tag = targetNode.tag ∧ next.parent = targetNode.parent ∧
        next.children = targetNode.children ∧ next.isExposed = targetNode.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin released.tree target .Write lower upper := by
  let registration := GeneralBorrowFnEntryRegistration.registered global {} allocation room
  let accessed := tree.performBorrowAccessRange (.concrete readerNode.tag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨_,readRuntime,readComplete,nodes,roots,tags,capacity,readOwned⟩ := CurrentCallOptionalLenAssociatedRead.prepare
    tree global allocation completion runtime complete primarySlot distinct order position root source reader rootNode readerNode primaryBelow rootSlot rootAt sourcePath
    readerAt readerPath readerEdge hidden readerUnheld room offset len bounds (by omega) readable owned
  obtain ⟨_,held,_,current,nodeFresh,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree global {} allocation room runtime
  have flags : ∀ index node, tree.nodes.get index = some node →
      registration.1.protectedTags.contains node.tag = global.protectedTags.contains node.tag := by
    intro index node present
    exact ProtectorInsertion.contains_other global.protectedTags global.nextPointerTag node.tag .StrongProtector
      (nodeFresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)))
  have targetRegistered : OwnedOn (Authority tree completion registration.1.protectedTags target) lower upper tree.locations := by
    intro cursor valid positive start stop index node present
    rw [flags index node present]
    exact targetOwned cursor valid positive start stop index node present
  have pointDisjoint : ∀ point : UInt64, lower.toNat ≤ point.toNat → point.toNat < upper.toNat →
      point.toNat < offset.toNat ∨ (offset+len).toNat ≤ point.toNat := by
    intro point start stop
    rcases disjoint with before | after <;> omega
  have targetAfter : accessed.tree.nodeAt target = some targetNode := by
    change accessed.tree.nodes.get target = _
    rw [nodes]
    exact targetAt
  have targetOwnedRead : OwnedOn (Authority accessed.tree completion registration.1.protectedTags target) lower upper accessed.tree.locations := by
    have retained := GeneralBorrowRangeOutsideOwned.owned (Authority tree completion registration.1.protectedTags target)
      tree (.concrete readerNode.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
      runtime.formed.well bounds lower upper pointDisjoint targetRegistered
    intro cursor valid positive start stop index node present
    exact retained cursor valid positive start stop index node (by rw [nodes] at present;exact present)
  have readRegistered : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location registration.1.protectedTags reader .Read))
      offset (offset+len) tree.locations := by
    intro cursor valid positive start stop
    obtain ⟨normal⟩ := readable cursor valid positive start stop
    have projection := GeneralBorrowProtector.normal_projection tree tree.locations.entries[cursor].data global.protectedTags
      global.nextPointerTag .StrongProtector nodeFresh
    refine ⟨⟨normal.component,?_⟩⟩
    intro index included bounded
    have table : registration.1.protectedTags = global.protectedTags.insert global.nextPointerTag .StrongProtector := rfl
    rw [table,projection]
    exact normal.permissions index included bounded
  have targetActiveRead : GeneralBorrowFreshActiveWithin.ActiveWithin accessed.tree target .Write lower upper :=
    CurrentCallReadRootActivity.concrete_of_normal tree registration.1 current readerNode.tag reader target readerNode readerAt
      offset len bounds readRegistered (runtime.formed.allocator.nodeTags reader readerNode readerAt)
      targetNode targetAt targetLeaf targetHidden different lower upper targetActive .VisitChildrenOfAccessed
  have present : accessed.tree.nodeAt reader = some readerNode := by change accessed.tree.nodes.get reader = _;rw [nodes];exact readerAt
  have tagged : accessed.tree.indexOfTag readerNode.tag = some reader := readRuntime.formed.allocator.nodeTags reader readerNode present
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [tags];exact fresh
  have nodeRoomAfter : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [nodes];exact nodeRoom
  have boundsAfter : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have heldTag : registration.1.protectedTags.contains global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  have tagBound : global.nextPointerTag.value.toNat < registration.1.nextPointerTag.value.toNat := by
    have step := GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat
    omega
  obtain ⟨_,childRuntime,_,_,helper,lookup,boolOwned⟩ := CurrentCallSharedConstructorFrame.disjoint accessed.tree registration.1 completion
    readRuntime readComplete readerNode.tag global.nextPointerTag reader target readerNode targetNode tagged present targetAfter freshAfter nodeRoomAfter
    tagBound true heldTag offset len lower upper nonzero boundsAfter pointDisjoint targetOwnedRead
  obtain ⟨⟨next,nextAt,nextTag,nextParent,nextChildren,nextHidden⟩,boolActive⟩ := S05SharedConstructorDisjoint.old_facets
    accessed.tree registration.1 readRuntime readerNode.tag global.nextPointerTag reader target readerNode targetNode tagged present targetAfter different
    freshAfter nodeRoomAfter true offset len nonzero boundsAfter .Write lower upper targetActiveRead
  let afterTree := (accessed.tree.newChild (Size.ofBytes offset) (.concrete readerNode.tag) global.nextPointerTag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree
  have normalRead : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability accessed.tree location registration.1.protectedTags reader .Read))
      offset (offset+len) accessed.tree.locations := fun cursor valid positive start stop => (readOwned cursor valid positive start stop).1
  obtain ⟨_,_,_,_,capHelper,capLookup,capabilities⟩ := GeneralBorrowSharedReadConstructor.construct accessed.tree registration.1
    readRuntime readerNode.tag global.nextPointerTag reader readerNode tagged present freshAfter nodeRoomAfter tagBound true heldTag offset len nonzero boundsAfter normalRead
  have capEq : capHelper = helper := Option.some.inj (capLookup.symm.trans lookup)
  subst capHelper
  obtain ⟨activeIndex,activeAt,activeWithin⟩ := (S05SharedChildActivity.construct accessed.tree registration.1 readRuntime readerNode.tag global.nextPointerTag
    reader readerNode tagged present freshAfter nodeRoomAfter tagBound true heldTag offset len nonzero boundsAfter).2
  have activeEq : activeIndex = helper := Option.some.inj (activeAt.symm.trans lookup)
  subst activeIndex
  obtain ⟨graphHelper,graphLookup,⟨helperNode,helperAt,helperTag,helperEdge,helperHidden⟩,_⟩ := GeneralBorrowSharedChildGraph.construct accessed.tree registration.1
    readRuntime readerNode.tag global.nextPointerTag reader readerNode tagged present freshAfter nodeRoomAfter true offset len nonzero boundsAfter
  have graphEq : graphHelper = helper := Option.some.inj (graphLookup.symm.trans lookup)
  subst graphHelper
  have helperWrite := GeneralBorrowFreshActiveWithin.to_write afterTree helper offset (offset+len) activeWithin
  have preserved := S02DisjointReleaseFrame.release afterTree registration.1.protectedTags global.nextPointerTag helper helper helperNode lookup helperAt helperHidden
    offset (offset+len) helperWrite helperWrite (Authority afterTree (extend completion helper reader) registration.1.protectedTags target)
    lower upper disjoint boolOwned childRuntime.formed.well
  have targetDifferent : target ≠ helper := by
    intro equal
    have same := Option.some.inj (nextAt.symm.trans (equal ▸ helperAt))
    have oldFresh := nodeFresh (target,targetNode) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes target targetNode).mpr targetAt))
    apply oldFresh
    exact nextTag.symm.trans ((congrArg TreeNode.tag same).trans helperTag)
  have boolActiveRelease := CurrentCallReadRootActivity.release afterTree registration.1 childRuntime global.nextPointerTag helper target helperNode next
    lookup helperAt helperHidden nextAt (nextChildren.trans targetLeaf) (nextHidden.trans targetHidden) targetDifferent
    offset (offset+len) lower upper activeWithin
    (fun cursor valid positive start stop => (capabilities cursor valid positive start stop).2) boolActive
  have releaseFrame := GeneralBorrowStructuralReleaseGeometryFrame.release afterTree registration.1.protectedTags global.nextPointerTag
  refine ⟨helper,lookup,?_,?_,boolActiveRelease⟩
  · intro cursor valid positive start stop index node nodeAt
    have oldAt : afterTree.nodes.get index = some node := by
      change (afterTree.releaseProtector global.nextPointerTag registration.1.protectedTags).tree.nodes.get index = some node at nodeAt
      rw [releaseFrame] at nodeAt
      exact nodeAt
    have authority := preserved cursor valid positive start stop index node oldAt
    have weaken := GeneralBorrowRelease.end_call_weakens registration.1 registration.2 node.tag
    refine ⟨?_,?_⟩
    · intro below
      obtain ⟨possible,disabled,frozen,reserved⟩ := authority.1 below
      exact ⟨possible,disabled,frozen,fun held => reserved (weaken held)⟩
    · intro outside
      obtain ⟨possible,quiet⟩ := authority.2 outside
      exact ⟨possible,fun held => quiet (weaken held)⟩
  · refine ⟨next,?_,nextTag,nextParent,nextChildren,nextHidden⟩
    change (afterTree.releaseProtector global.nextPointerTag registration.1.protectedTags).tree.nodeAt target = some next
    rw [releaseFrame]
    exact nextAt

end DuplicatePrefix.CurrentCallOptionalLenBoolFrame
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOptionalLenBoolFrame").length > 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved Len shared Bool frame dependency {dependency}"
