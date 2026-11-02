import duplicate_prefix.CurrentCallResourceSourceActivity
import duplicate_prefix.CurrentCallResourceLenReturn
import duplicate_prefix.GeneralBorrowRawTargetActivity

namespace DuplicatePrefix.CurrentCallResourceLenActivity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
open GeneralRangeMapOrigins GeneralBorrowFnEntryRegistration GeneralBorrowRawSharedExpression
open S05ConcreteProtectedChildCompletion
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

private theorem release_nodes (tree : BorrowTree) (flags : ProtectedTags) (tag : BorTag) :
    (tree.releaseProtector tag flags).tree.nodes=tree.nodes := by
  have nodes:=congrArg BorrowTree.nodes (GeneralBorrowStructuralReleaseGeometryFrame.release tree flags tag)
  exact nodes

private theorem release_roots (tree : BorrowTree) (flags : ProtectedTags) (tag : BorTag) :
    (tree.releaseProtector tag flags).tree.roots=tree.roots := by
  have roots:=congrArg BorrowTree.roots (GeneralBorrowStructuralReleaseGeometryFrame.release tree flags tag)
  exact roots

private theorem shared {before tracker data owner id offset length}
    (Q : UniformWindow before tracker data owner id offset length .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra tracker.global)
    (tag : BorTag) (concrete : Q.pointer.value.provenance=.concrete id tag)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (nodeRoom : Q.allocation.extra.nodes.size+1≤4294967295)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤Q.allocation.extra.locations.size.bytes.toNat)
    (P : CurrentCallResourceDefaultShared.Preparation Q tag start amount room)
    (target : UniIndex) (node : TreeNode) (targetAt : Q.allocation.extra.nodes.get target=some node)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra target .Write start (start+amount)) :
    let actual:=(child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree
    (∃ next,actual.nodes.get target=some next ∧next.tag=node.tag ∧next.parent=node.parent ∧next.isExposed=node.isExposed) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin actual target .Write start (start+amount) ∧
    (∀ query oldNode,Q.allocation.extra.nodes.get query=some oldNode →
      ∃ next,actual.nodes.get query=some next ∧next.tag=oldNode.tag ∧next.parent=oldNode.parent ∧next.isExposed=oldNode.isExposed) ∧
    actual.roots=Q.allocation.extra.roots := by
  let after:=read Q.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed
  have readActive:=GeneralBorrowFreshActiveWithinAccess.normal Q.allocation.extra tag (Size.ofBytes start) (Size.ofBytes amount) .Read
    tracker.global.protectedTags .VisitChildrenOfAccessed target start (start+amount) runtime.formed.well bounds (Nat.le_refl _) (Nat.le_refl _) activity
  have high:=GeneralBorrowForestTagHighWater.complete Q.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,_⟩:=GenericFunctionTagFormation.fresh_above Q.allocation.extra _ _ tracker.global.nextPointerTag high (Nat.le_refl _)
  obtain ⟨parent,parentAt,_,binding⟩:=Q.binding
  rw [concrete] at binding
  have present : after.tree.nodeAt Q.pointer.grant=some parent := by change after.tree.nodes.get _=_;rw [P.nodes];exact parentAt
  have tagged : after.tree.indexOfTag tag=some Q.pointer.grant := by rw [binding.2];exact P.runtime.formed.allocator.nodeTags _ _ present
  have freshAfter : GeneralBorrowTagMap.Fresh after.tree.tagMapping tracker.global.nextPointerTag := by rw [P.tags];exact fresh
  have roomAfter : after.tree.nodes.size+1≤4294967295 := by change after.tree.nodes.data.size+1≤_;rw [P.nodes];exact nodeRoom
  have boundsAfter : start.toNat+amount.toNat≤after.tree.locations.size.bytes.toNat := by rw [P.capacity];exact bounds
  have targetAfter : after.tree.nodeAt target=some node := by change after.tree.nodes.get _=_;rw [P.nodes];exact targetAt
  obtain ⟨_,_,_,old⟩:=GeneralBorrowSharedChildGraph.construct after.tree (advanced tracker.global room) P.runtime tag tracker.global.nextPointerTag
    Q.pointer.grant parent tagged present freshAfter roomAfter false start amount nonzero boundsAfter
  refine ⟨old target node targetAfter,GeneralBorrowRawTargetActivity.shared after.tree (advanced tracker.global room) P.runtime
    tag tracker.global.nextPointerTag Q.pointer.grant parent tagged present freshAfter roomAfter false start amount nonzero boundsAfter
    target start (start+amount) (Nat.le_refl _) (Nat.le_refl _) readActive,?_,?_⟩
  · intro query oldNode found
    exact old query oldNode (by change after.tree.nodes.get _=_;rw [P.nodes];exact found)
  · obtain ⟨_,_,metadata⟩:=GeneralBorrowSharedReadMetadata.construct after.tree (advanced tracker.global room) P.runtime
      tag tracker.global.nextPointerTag Q.pointer.grant parent tagged present freshAfter roomAfter false start amount nonzero boundsAfter
    exact metadata.roots.trans P.roots

variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : Output limits C count) (ready : CurrentCallResourceBodyReadiness.Ready C)

structure Frame {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len
      (CurrentCallResourceBodyReadiness.current_room out ready)}
    (returned : CurrentCallResourceLenReturn.Result out ready Q stage) : Prop where
  hidden : returned.sourceNode.isExposed=false
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallResourceLenReturn.releasedTree out ready) out.sourceChild .Write
    (UInt64.ofNat offset) (UInt64.ofNat offset+len)
  roots : (CurrentCallResourceLenReturn.releasedTree out ready).roots=Q.allocation.extra.roots
  metadata : ∀ query node,Q.allocation.extra.nodes.get query=some node →
    ∃ next,(CurrentCallResourceLenReturn.releasedTree out ready).nodes.get query=some next ∧
      next.tag=node.tag ∧next.parent=node.parent ∧next.isExposed=node.isExposed
  below : ∀ ancestor target,Below Q.precise.completion ancestor target →Below returned.completion ancestor target
  edges : ∀ (query parent : UniIndex),Q.precise.completion.parents[query.toNat]?=some (some parent) →
    returned.completion.parents[query.toNat]?=some (some parent)

/-- The actual source remains active only inside its original window through
the shared reader, Strong helper and actual release. No source-leaf premise
is imposed after descendants have been installed. -/
theorem resources {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len
      (CurrentCallResourceBodyReadiness.current_room out ready)}
    (returned : CurrentCallResourceLenReturn.Result out ready Q stage) :
    Frame out ready returned := by
  obtain ⟨oldNode,oldAt,oldTag,_,oldHidden,oldActivity⟩:=CurrentCallResourceSourceActivity.current out
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra out.boolOutput.global := by rw [returned.sourceAllocation];exact CurrentCallResourceSourceFinal.runtime out
  have sourceBounds:=CurrentCallResourceSharedStage.source_bounds out
  have bounds : (UInt64.ofNat offset).toNat+len.toNat≤Q.allocation.extra.locations.size.bytes.toNat := by rw [returned.sourceAllocation];exact sourceBounds.2
  have nodeRoom : Q.allocation.extra.nodes.size+1≤4294967295 := by rw [returned.sourceAllocation];have room:=CurrentCallResourceBodyReadiness.current_nodes out ready;omega
  have nonzero : len≠0:=by intro zero;have positive:=C.positive;rw [zero] at positive;contradiction
  have concrete : Q.pointer.value.provenance=.concrete id out.sourceOutput.tag := by rw [returned.sourcePointer];rfl
  have oldAtQ : Q.allocation.extra.nodes.get out.sourceChild=some oldNode := by rw [returned.sourceAllocation];exact oldAt
  have oldActiveQ : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra out.sourceChild .Write (UInt64.ofNat offset) (UInt64.ofNat offset+len) := by rw [returned.sourceAllocation];exact oldActivity
  obtain ⟨⟨node,nodeAt,nodeTag,nodeParent,nodeHidden⟩,sharedActivity,oldR,rRoots⟩:=shared Q runtime out.sourceOutput.tag concrete
    (CurrentCallResourceBodyReadiness.current_room out ready) (UInt64.ofNat offset) len nodeRoom nonzero bounds stage.preparation
    out.sourceChild oldNode oldAtQ oldActiveQ
  have treeEq : (child Q.allocation.extra out.boolOutput.global.protectedTags out.sourceOutput.tag out.boolOutput.global.nextPointerTag
      (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree=CurrentCallResourceSharedStage.tree out := by
    dsimp only [CurrentCallResourceSharedStage.tree]
    exact congrArg (fun a : Allocation Provenance BorrowTree=>(child a.extra out.boolOutput.global.protectedTags out.sourceOutput.tag out.boolOutput.global.nextPointerTag
      (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree) returned.sourceAllocation
  rw [treeEq] at nodeAt sharedActivity oldR rRoots
  obtain ⟨P⟩:=CurrentCallResourceLenReturn.preStrongSnapshot out ready Q returned.sourcePointer returned.sourceAllocation stage
  let global:=(CurrentCallResourceLenInvoke.held out ready).global
  let reg:=registered global {} id (CurrentCallResourceLenInvoke.helper_room out ready)
  obtain ⟨_,afterRuntime,afterParents,nodes,readRoots,tags,capacity,_⟩:=CurrentCallOptionalLenAssociatedRead.prepare
    (CurrentCallResourceSharedStage.tree out) global id _ P.runtime P.parents P.primarySlot P.distinct P.parents.order
    stage.preparation.geometry.selectedPosition stage.preparation.geometry.selectedRoot Q.pointer.grant stage.reader P.rootNode P.readerNode
    P.primaryBelow P.rootSlot P.rootAt P.sourcePath P.readerAt P.readerPath P.readerEdge P.readerHidden P.readerUnheld
    (CurrentCallResourceLenInvoke.helper_room out ready) (UInt64.ofNat offset) len P.bounds (by have margin:=P.margin;omega) P.readable P.owned
  let accessed:=(CurrentCallResourceSharedStage.tree out).performBorrowAccessRange (.concrete P.readerNode.tag)
    (Size.ofBytes (UInt64.ofNat offset)) (Size.ofBytes len) .Read reg.1.protectedTags .VisitChildrenOfAccessed
  have readActivity:=GeneralBorrowFreshActiveWithinAccess.normal (CurrentCallResourceSharedStage.tree out) P.readerNode.tag
    (Size.ofBytes (UInt64.ofNat offset)) (Size.ofBytes len) .Read reg.1.protectedTags .VisitChildrenOfAccessed out.sourceChild
    (UInt64.ofNat offset) (UInt64.ofNat offset+len) P.runtime.formed.well P.bounds (Nat.le_refl _) (Nat.le_refl _) sharedActivity
  obtain ⟨_,_,_,_,freshNodes,fresh⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare (CurrentCallResourceSharedStage.tree out) global {} id
    (CurrentCallResourceLenInvoke.helper_room out ready) P.runtime
  have readerAt : accessed.tree.nodeAt stage.reader=some P.readerNode := by change accessed.tree.nodes.get _=_;rw [nodes];exact P.readerAt
  have tagged : accessed.tree.indexOfTag P.readerNode.tag=some stage.reader := afterRuntime.formed.allocator.nodeTags _ _ readerAt
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [tags];exact fresh
  have roomAfter : accessed.tree.nodes.size+1≤4294967295 := by rw [nodes];have margin:=P.margin;omega
  have boundsAfter : (UInt64.ofNat offset).toNat+len.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact P.bounds
  have targetAt : accessed.tree.nodeAt out.sourceChild=some node := by change accessed.tree.nodes.get _=_;rw [nodes];exact nodeAt
  have helperActivity:=GeneralBorrowRawTargetActivity.shared accessed.tree reg.1 afterRuntime P.readerNode.tag global.nextPointerTag stage.reader P.readerNode
    tagged readerAt freshAfter roomAfter true (UInt64.ofNat offset) len nonzero boundsAfter out.sourceChild
    (UInt64.ofNat offset) (UInt64.ofNat offset+len) (Nat.le_refl _) (Nat.le_refl _) readActivity
  obtain ⟨helper,lookup,⟨helperNode,helperAt,helperTag,_,helperHidden⟩,oldH⟩:=GeneralBorrowSharedChildGraph.construct accessed.tree reg.1 afterRuntime
    P.readerNode.tag global.nextPointerTag stage.reader P.readerNode tagged readerAt freshAfter roomAfter true (UInt64.ofNat offset) len nonzero boundsAfter
  obtain ⟨_,_,hMetadata⟩:=GeneralBorrowSharedReadMetadata.construct accessed.tree reg.1 afterRuntime
    P.readerNode.tag global.nextPointerTag stage.reader P.readerNode tagged readerAt freshAfter roomAfter true (UInt64.ofNat offset) len nonzero boundsAfter
  obtain ⟨next,nextAt,nextTag,nextParent,nextHidden⟩:=oldH out.sourceChild node targetAt
  obtain ⟨activityIndex,activityLookup,active⟩:=GeneralBorrowConstructorChildActivity.Shared.construct accessed.tree reg.1 afterRuntime
    P.readerNode.tag global.nextPointerTag stage.reader P.readerNode tagged readerAt freshAfter roomAfter true (UInt64.ofNat offset) len nonzero boundsAfter
  have same : activityIndex=helper:=Option.some.inj (activityLookup.symm.trans lookup)
  subst activityIndex
  have helperWrite:=GeneralBorrowFreshActiveWithin.to_write _ helper (UInt64.ofNat offset) (UInt64.ofNat offset+len) active
  have releasedActivity:=GeneralBorrowActiveWithinRelease.release _ reg.1.protectedTags global.nextPointerTag helper out.sourceChild helperNode
    lookup helperAt helperHidden (UInt64.ofNat offset) (UInt64.ofNat offset+len) helperWrite helperActivity
  have high:=GeneralBorrowForestTagHighWater.complete Q.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨_,freshR,_⟩:=GenericFunctionTagFormation.fresh_above Q.allocation.extra _ _ out.boolOutput.global.nextPointerTag high (Nat.le_refl _)
  have vacantR : Q.allocation.extra.nodes.get stage.reader=none := by
    cases original : Q.allocation.extra.nodes.get stage.reader with
    | none=>rfl
    | some oldNode=>
      obtain ⟨changed,changedAt,changedTag,_,_⟩:=oldR stage.reader oldNode original
      have equal : changed=P.readerNode:=Option.some.inj (changedAt.symm.trans P.readerAt)
      exact False.elim (freshR (stage.reader,oldNode)
        (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get Q.allocation.extra.nodes stage.reader oldNode).mpr original))
        (changedTag.symm.trans ((congrArg TreeNode.tag equal).trans P.readerTag)))
  have vacantH : accessed.tree.nodes.get helper=none := by
    cases original : accessed.tree.nodes.get helper with
    | none=>rfl
    | some oldNode=>
      obtain ⟨changed,changedAt,changedTag,_,_⟩:=oldH helper oldNode original
      have equal : changed=helperNode:=Option.some.inj (changedAt.symm.trans helperAt)
      have originalAt : (CurrentCallResourceSharedStage.tree out).nodes.get helper=some oldNode:=by rw [←nodes];exact original
      exact False.elim (freshNodes (helper,oldNode)
        (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get (CurrentCallResourceSharedStage.tree out).nodes helper oldNode).mpr originalAt))
        (changedTag.symm.trans ((congrArg TreeNode.tag equal).trans helperTag)))
  have releaseFrame:=release_nodes
    (accessed.tree.newChild (Size.ofBytes (UInt64.ofNat offset)) (.concrete P.readerNode.tag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree reg.1.protectedTags global.nextPointerTag
  have rootsEq:=(release_roots (accessed.tree.newChild (Size.ofBytes (UInt64.ofNat offset)) (.concrete P.readerNode.tag) global.nextPointerTag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree reg.1.protectedTags global.nextPointerTag).trans
      (hMetadata.roots.trans (readRoots.trans rRoots))
  have releasedAt:=nextAt
  dsimp only [BorrowTree.nodeAt] at releasedAt
  rw [←releaseFrame] at releasedAt
  have actualTree : (accessed.tree.newChild (Size.ofBytes (UInt64.ofNat offset)) (.concrete P.readerNode.tag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree=CurrentCallResourceLenInvoke.borrowedTree out ready := by
    dsimp only [accessed]
    rw [P.readerTag]
    rfl
  rw [actualTree] at releasedActivity releasedAt lookup rootsEq
  have flags : reg.1.protectedTags=(CurrentCallResourceLenReturn.liveTracker out ready).global.protectedTags:=rfl
  have releasedEq : ((CurrentCallResourceLenInvoke.borrowedTree out ready).releaseProtector global.nextPointerTag reg.1.protectedTags).tree=
      CurrentCallResourceLenReturn.releasedTree out ready := by dsimp only [CurrentCallResourceLenReturn.releasedTree];rw [flags]
  rw [releasedEq] at releasedActivity releasedAt rootsEq
  have helperEq : helper=returned.helperIndex:=Option.some.inj (lookup.symm.trans returned.lookup)
  subst helper
  have grant : Q.pointer.grant=out.sourceChild := congrArg PointerInstance.grant returned.sourcePointer
  have nodeEq : next=returned.sourceNode:=Option.some.inj (releasedAt.symm.trans (by rw [←grant];exact returned.sourceAt))
  refine ⟨by rw [←nodeEq,nextHidden,nodeHidden];exact oldHidden,releasedActivity,rootsEq,?_,?_,?_⟩
  · intro query oldNode found
    obtain ⟨middle,middleAt,middleTag,middleParent,middleExposed⟩:=oldR query oldNode found
    have readAt : accessed.tree.nodeAt query=some middle:=by change accessed.tree.nodes.get _=_;rw [nodes];exact middleAt
    obtain ⟨next,nextAt,tag,parent,exposed⟩:=oldH query middle readAt
    have currentAt:=nextAt
    dsimp only [BorrowTree.nodeAt] at currentAt
    rw [←releaseFrame,actualTree,releasedEq] at currentAt
    exact ⟨next,currentAt,tag.trans middleTag,parent.trans middleParent,exposed.trans middleExposed⟩
  · intro ancestor target path
    have earlier:=CurrentCallResourceChild.old_ancestry Q.allocation.extra Q.precise.completion Q.parents stage.reader Q.pointer.grant vacantR path
    exact CurrentCallResourceChild.old_ancestry accessed.tree (extend Q.precise.completion stage.reader Q.pointer.grant) afterParents
      returned.helperIndex stage.reader vacantH earlier
  · intro query parent edge
    have queryAt:=(Q.parents.edgeLive query parent edge).1
    have neR : query≠stage.reader:=by intro equal;obtain ⟨node,atNode⟩:=queryAt;rw [equal,vacantR] at atNode;cases atNode
    have first : (extend Q.precise.completion stage.reader Q.pointer.grant).parents[query.toNat]?=some (some parent):=
      (old_parent Q.precise.completion stage.reader Q.pointer.grant query neR (Array.getElem?_eq_some_iff.mp edge).1).trans edge
    have secondAt:=(afterParents.edgeLive query parent first).1
    have neH : query≠returned.helperIndex:=by intro equal;obtain ⟨node,atNode⟩:=secondAt;rw [equal,vacantH] at atNode;cases atNode
    exact (old_parent (extend Q.precise.completion stage.reader Q.pointer.grant) returned.helperIndex stage.reader query neH
      (Array.getElem?_eq_some_iff.mp first).1).trans first

theorem current {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len
      (CurrentCallResourceBodyReadiness.current_room out ready)}
    (returned : CurrentCallResourceLenReturn.Result out ready Q stage) :
    returned.sourceNode.isExposed=false ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallResourceLenReturn.releasedTree out ready) out.sourceChild .Write
      (UInt64.ofNat offset) (UInt64.ofNat offset+len) :=
  ⟨(resources out ready returned).hidden,(resources out ready returned).activity⟩

end
end DuplicatePrefix.CurrentCallResourceLenActivity
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceLenActivity" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual Len activity dependency {dependency}"
