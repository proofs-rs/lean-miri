import duplicate_prefix.CurrentCallResourceLenReturn
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometryFrame

namespace DuplicatePrefix.CurrentCallResourceLenCapability
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallResourceEntryBody GeneralBorrowFnEntryRegistration GeneralBorrowRawSharedExpression
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder GeneralRangeMapOrigins
open S05ConcreteProtectedChildCompletion
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Actual optional parent edges issue a finite spatial path from the canonical
allocation capability; no new virtual origin is selected. -/
theorem issued_of_rootBelow {before tracker id allocation completion grant}
    (cap : AllocationCapability before tracker id allocation)
    (parents : ParentInterpretation allocation.extra completion)
    (below : Below completion allocationRoot grant) :
    SpatialDelegation before tracker id allocation completion grant := by
  induction below with
  | refl => exact .allocated cap
  | @step parent child edge prior ih =>
    obtain ⟨⟨childNode,childAt⟩,⟨parentNode,parentAt⟩⟩ := parents.edgeLive child parent edge
    cases physical : childNode.parent with
    | some actualParent =>
      have same : actualParent=parent := Option.some.inj (Option.some.inj
        ((parents.physical child childNode childAt actualParent physical).symm.trans edge))
      subst actualParent
      exact .concrete ih (.step (.refl parent parentNode parentAt) childNode childAt physical)
    | none =>
      obtain ⟨position,slot⟩ := Array.getElem?_of_mem
        (Array.mem_toList_iff.mp (parents.graph.covered child childNode childAt physical))
      obtain ⟨earlier,originRoot,rootNode,originNode,olderPosition,originSlot,rootAt,originAt,exposed,older,path⟩ :=
        parents.virtual position child slot parent edge
      have same : rootNode=childNode := Option.some.inj (rootAt.symm.trans childAt)
      subst rootNode
      exact .wildcard originNode childNode earlier position originRoot ih originAt exposed childAt physical older
        olderPosition originSlot slot path edge

private theorem shared_held_tree (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag=some parent) (present : tree.nodeAt parent=some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1≤4294967295)
    (first second : Bool) (offset len : UInt64) (nonzero : len≠0)
    (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat) :
    (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen first).tree=
    (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen second).tree := by
  let rank:=GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  cases GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,first,offset,len,nonzero,runtime.formed.well,bounds⟩
    change GeneralBorrowFreshMetadataChildShared.result input=GeneralBorrowFreshMetadataChildShared.result {input with isProtected:=second}
    rw [GeneralBorrowFreshMetadataChildShared.tree_eq,GeneralBorrowFreshMetadataChildShared.tree_eq]
    rfl
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,bounded,vacant,slack,first,offset,len,nonzero,runtime.formed.well,bounds⟩
    change GeneralBorrowFreshMetadataChildSharedReuse.result input=GeneralBorrowFreshMetadataChildSharedReuse.result {input with isProtected:=second}
    rw [GeneralBorrowFreshMetadataChildSharedReuse.tree_eq,GeneralBorrowFreshMetadataChildSharedReuse.tree_eq]
    rfl

private theorem absent_runtime (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (allocation : AllocId) (tag : BorTag)
    (absent : ∀ index node,tree.nodeAt index=some node → node.tag≠tag) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree (global.endCall (({} : FrameState).addProtector allocation tag)) := by
  have flags : (global.endCall (({} : FrameState).addProtector allocation tag)).protectedTags=global.protectedTags.remove tag := by
    simp only [GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty]
  refine ⟨⟨runtime.formed.toState,?_⟩,?_,runtime.possible,?_⟩
  · intro cursor valid
    rw [flags]
    exact GeneralBorrowHiddenProtectorDropRuntime.profile tree _ _ _ (GeneralBorrowRelease.remove_weakens global.protectedTags tag)
      (runtime.formed.profile cursor valid)
  · intro cursor valid
    rw [flags]
    apply GeneralBorrowProtectorCacheMap.remove_hidden tree _ global.protectedTags tag (runtime.coherent cursor valid)
    intro index node present tagged
    exact False.elim (absent index node present tagged)
  · refine ⟨runtime.below.mapping,?_⟩
    intro row member
    rw [flags] at member
    exact runtime.below.protectors row (Array.mem_filter.mp member).1


private def associated (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (room : global.nextPointerTag.value<18446744073709551615) (tag : BorTag) (offset len : UInt64) :=
  tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len) .Read
    (registered global {} allocation room).1.protectedTags .VisitChildrenOfAccessed

private def strongTree (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (room : global.nextPointerTag.value<18446744073709551615) (tag : BorTag) (offset len : UInt64) :=
  ((associated tree global allocation room tag offset len).tree.newChild (Size.ofBytes offset) (.concrete tag) global.nextPointerTag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree

private theorem helper_root (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (parents : ParentInterpretation tree completion)
    (primarySlot : tree.roots[0]?=some allocationRoot) (distinct : tree.roots.toList.Nodup)
    (source reader : UniIndex) (sourceNode readerNode : TreeNode)
    (sourceAt : tree.nodes.get source=some sourceNode) (readerAt : tree.nodeAt reader=some readerNode)
    (readerEdge : readerNode.parent=some source) (readerHidden : readerNode.isExposed=false)
    (readerUnheld : global.protectedTags.contains readerNode.tag=false)
    (primaryBelow : Below completion allocationRoot source)
    (allocation : AllocId) (room : global.nextPointerTag.value<18446744073709551615)
    (offset len : UInt64) (nonzero : len≠0)
    (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat) (nodeMargin : tree.nodes.size+1<65536)
    (readable : OwnedOn (fun location=>Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read)) offset (offset+len) tree.locations)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags source) offset (offset+len) tree.locations)
    (zero : TreeNode) (zeroAt : tree.nodes.get allocationRoot=some zero) :
    let actual:=strongTree tree global allocation room readerNode.tag offset len
    actual.roots[0]?=some allocationRoot ∧
      ∃ next,actual.nodes.get allocationRoot=some next ∧ next.tag=zero.tag ∧ next.parent=zero.parent ∧ next.defaultInitialPermission=zero.defaultInitialPermission := by
  let registration:=registered global {} allocation room
  let frame:=({} : FrameState).addProtector allocation global.nextPointerTag
  let accessed:=associated tree global allocation room readerNode.tag offset len
  let actual:=strongTree tree global allocation room readerNode.tag offset len
  obtain ⟨position,root,rootNode,rootSlot,rootAt,sourcePath⟩:=CandidateCurrentWindowAuthority.root_path tree parents.graph source sourceNode sourceAt
  have readerPath : Path tree root reader:=.step sourcePath readerNode readerAt readerEdge
  obtain ⟨_,afterRuntime,_,nodes,roots,tags,capacity,_⟩:=CurrentCallOptionalLenAssociatedRead.prepare tree global allocation completion runtime parents
    primarySlot distinct parents.order position root source reader rootNode readerNode primaryBelow rootSlot rootAt sourcePath readerAt readerPath readerEdge readerHidden readerUnheld
    room offset len bounds (by omega) readable owned
  change DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 at afterRuntime
  change accessed.tree.nodes=tree.nodes at nodes
  change accessed.tree.roots=tree.roots at roots
  change accessed.tree.tagMapping=tree.tagMapping at tags
  change accessed.tree.locations.size=tree.locations.size at capacity
  obtain ⟨_,_,_,_,nodeFresh,fresh⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare tree global {} allocation room runtime
  have readerAfter : accessed.tree.nodeAt reader=some readerNode:=by change accessed.tree.nodes.get _=_;rw [nodes];exact readerAt
  have tagged : accessed.tree.indexOfTag readerNode.tag=some reader:=afterRuntime.formed.allocator.nodeTags _ _ readerAfter
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag:=by rw [tags];exact fresh
  have nodeFreshAfter : GeneralBorrowProtector.Fresh accessed.tree global.nextPointerTag:=by simpa only [GeneralBorrowProtector.Fresh,nodes] using nodeFresh
  have nodeRoom : accessed.tree.nodes.size+1≤4294967295:=by rw [nodes];omega
  have currentBounds : offset.toNat+len.toNat≤accessed.tree.locations.size.bytes.toNat:=by rw [capacity];exact bounds
  have tagBound : global.nextPointerTag.value.toNat<registration.1.nextPointerTag.value.toNat:=by
    have successor:=GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    change global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat
    omega
  let future:=registration.1.endCall frame
  have futureRuntime : DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree future:=absent_runtime accessed.tree registration.1 afterRuntime allocation global.nextPointerTag
    (by intro index node present;exact nodeFreshAfter (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get accessed.tree.nodes index node).mpr present)))
  have unheld : future.protectedTags.contains global.nextPointerTag=false:=by
    change (registration.1.protectedTags.remove global.nextPointerTag).contains global.nextPointerTag=false
    simp only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none]
  have heldEq:=shared_held_tree accessed.tree registration.1 afterRuntime readerNode.tag global.nextPointerTag reader readerNode tagged readerAfter freshAfter nodeRoom true false offset len nonzero currentBounds
  obtain ⟨_,_,_,_,helper,lookup,leaf,old⟩:=CurrentCallSharedConstructorFrame.metadata accessed.tree future futureRuntime readerNode.tag global.nextPointerTag reader readerNode
    tagged readerAfter freshAfter nodeRoom tagBound unheld offset len nonzero currentBounds
  rw [←heldEq] at leaf old
  change S05ConcreteProtectedChildCompletion.LeafFrame accessed.tree actual helper reader at leaf
  have zeroAfter : accessed.tree.nodeAt allocationRoot=some zero:=by change accessed.tree.nodes.get _=_;rw [nodes];exact zeroAt
  obtain ⟨next,nextAt,nextTag,nextParent,_,nextPermission⟩:=old allocationRoot zero zeroAfter
  refine ⟨?_,next,nextAt,nextTag,nextParent,nextPermission⟩
  rw [leaf.roots,roots]
  exact primarySlot

variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : Output limits C count) (ready : CurrentCallResourceBodyReadiness.Ready C)

private theorem stage_root {nextData nextOwner}
    (Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut)
    (pointer : Q.pointer=CurrentCallResourceSourceAfterBool.pointer out)
    (allocation : Q.allocation=(CurrentCallResourceSourceFinal.entry out).allocation)
    (stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)) :
    ∃ node,(CurrentCallResourceSharedStage.tree out).nodes.get allocationRoot=some node ∧
      node.parent=none ∧ node.defaultInitialPermission=.Disabled ∧ out.boolOutput.global.rootTag? id=some node.tag := by
  let global:=out.boolOutput.global
  let room:=CurrentCallResourceBodyReadiness.current_room out ready
  let P:=stage.preparation
  let accessed:=read Q.allocation.extra global.protectedTags out.sourceOutput.tag (UInt64.ofNat offset) len .VisitChildrenOfAccessed
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra global:=by rw [allocation];exact CurrentCallResourceSourceFinal.runtime out
  have nodeRoom : Q.allocation.extra.nodes.size+1≤4294967295:=by rw [allocation];have budget:=CurrentCallResourceBodyReadiness.current_nodes out ready;omega
  have concrete : Q.pointer.value.provenance=.concrete id out.sourceOutput.tag:=by rw [pointer];rfl
  have nonzero : len≠0:=by intro zero;have p:=C.positive;rw [zero] at p;contradiction
  have bounds : (UInt64.ofNat offset).toNat+len.toNat≤Q.allocation.extra.locations.size.bytes.toNat:=by rw [allocation];exact (CurrentCallResourceSharedStage.source_bounds out).2
  have high:=GeneralBorrowForestTagHighWater.complete Q.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩:=GenericFunctionTagFormation.fresh_above Q.allocation.extra _ _ global.nextPointerTag high (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag:=by rw [P.tags];exact fresh
  obtain ⟨parent,parentAt,_,binding⟩:=Q.binding
  rw [concrete] at binding
  have parentAfter : accessed.tree.nodeAt Q.pointer.grant=some parent:=by change accessed.tree.nodes.get _=_;rw [P.nodes];exact parentAt
  have tagged : accessed.tree.indexOfTag out.sourceOutput.tag=some Q.pointer.grant:=by rw [binding.2];exact P.runtime.formed.allocator.nodeTags _ _ parentAfter
  have roomAfter : accessed.tree.nodes.size+1≤4294967295:=by change accessed.tree.nodes.data.size+1≤_;rw [P.nodes];exact nodeRoom
  have boundsAfter : (UInt64.ofNat offset).toNat+len.toNat≤accessed.tree.locations.size.bytes.toNat:=by rw [P.capacity];exact bounds
  have tagBound : global.nextPointerTag.value.toNat<(advanced global room).nextPointerTag.value.toNat:=by
    have successor:=GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    change global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat
    omega
  obtain ⟨_,_,_,_,reader,lookup,leaf,old⟩:=CurrentCallSharedConstructorFrame.metadata accessed.tree (advanced global room) P.runtime
    out.sourceOutput.tag global.nextPointerTag Q.pointer.grant parent tagged parentAfter freshAfter roomAfter tagBound unheld
    (UInt64.ofNat offset) len nonzero boundsAfter
  obtain ⟨zero,zeroAt,zeroParent,zeroDisabled,zeroTag⟩:=Q.issued.capability.rootNode
  have zeroAfter : accessed.tree.nodeAt allocationRoot=some zero:=by change accessed.tree.nodes.get _=_;rw [P.nodes];exact zeroAt
  obtain ⟨next,nextAt,nextTag,nextParent,_,nextPermission⟩:=old allocationRoot zero zeroAfter
  have treeEq : (child Q.allocation.extra global.protectedTags out.sourceOutput.tag global.nextPointerTag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree=
      CurrentCallResourceSharedStage.tree out:=by rw [allocation];rfl
  change (child Q.allocation.extra global.protectedTags out.sourceOutput.tag global.nextPointerTag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree.nodes.get allocationRoot=some next at nextAt
  rw [treeEq] at nextAt
  exact ⟨next,nextAt,nextParent.trans zeroParent,nextPermission.trans zeroDisabled,by rw [nextTag];exact zeroTag⟩


def sourceAllocation := (CurrentCallResourceLenInvoke.entry out).allocation.setExtra (CurrentCallResourceLenReturn.releasedTree out ready)

variable {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    (returned : CurrentCallResourceLenReturn.Result out ready Q stage)

private theorem present_of_live (machine : Before) (allocationId : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (found : machine.memory.live.find? (fun row=>row.1==allocationId)=some (allocationId,entry)) :
    Present (ActualWorld machine) allocationId entry.allocation := by
  simp only [Present,ActualWorld,Array.toList_map]
  exact List.mem_map.mpr ⟨(allocationId,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found),rfl⟩

theorem present : Present (ActualWorld returned.machine) id (sourceAllocation out ready) := by
  have actual:=present_of_live returned.machine id _ returned.sourceLive
  simpa only [sourceAllocation] using actual

include returned in
theorem source_len : (sourceAllocation out ready).len=Q.allocation.len := by
  have equal:=congrArg Allocation.len returned.sourceAllocation
  simpa only [sourceAllocation,CurrentCallResourceLenInvoke.entry,Allocation.setExtra,Allocation.mapExtra,Allocation.len] using equal.symm

include returned in
theorem source_byteSize : (sourceAllocation out ready).byteSize=Q.allocation.byteSize := by
  have equal:=congrArg Allocation.byteSize returned.sourceAllocation
  simpa only [sourceAllocation,CurrentCallResourceLenInvoke.entry,Allocation.setExtra,Allocation.mapExtra,Allocation.byteSize] using equal.symm

/-- The canonical root capability survives the SAME constructors and release. -/
theorem capability : AllocationCapability returned.machine (CurrentCallResourceLenReturn.postTracker out ready) id (sourceAllocation out ready) := by
  obtain ⟨snapshot⟩:=CurrentCallResourceLenReturn.preStrongSnapshot out ready Q returned.sourcePointer returned.sourceAllocation stage
  obtain ⟨zero,zeroAt,zeroParent,zeroDisabled,zeroTag⟩:=stage_root out ready Q returned.sourcePointer returned.sourceAllocation stage
  have nonzero : len≠0:=by intro zero;have positive:=C.positive;rw [zero] at positive;contradiction
  obtain ⟨rootSlot,next,nextAt,nextTag,nextParent,nextPermission⟩:=helper_root
    (CurrentCallResourceSharedStage.tree out) (CurrentCallResourceLenInvoke.held out ready).global
    (extend Q.precise.completion stage.reader Q.pointer.grant) snapshot.runtime snapshot.parents snapshot.primarySlot snapshot.distinct
    Q.pointer.grant stage.reader snapshot.sourceNode snapshot.readerNode snapshot.sourceAt snapshot.readerAt snapshot.readerEdge snapshot.readerHidden snapshot.readerUnheld
    snapshot.primaryBelow id (CurrentCallResourceLenInvoke.helper_room out ready) (UInt64.ofNat offset) len nonzero snapshot.bounds snapshot.margin snapshot.readable snapshot.owned zero zeroAt
  have actualTree : strongTree (CurrentCallResourceSharedStage.tree out) (CurrentCallResourceLenInvoke.held out ready).global id
      (CurrentCallResourceLenInvoke.helper_room out ready) snapshot.readerNode.tag (UInt64.ofNat offset) len=CurrentCallResourceLenInvoke.borrowedTree out ready := by
    rw [snapshot.readerTag]
    rfl
  rw [actualTree] at rootSlot nextAt
  have releasedFrame:=GeneralBorrowStructuralReleaseGeometryFrame.release (CurrentCallResourceLenInvoke.borrowedTree out ready)
    (CurrentCallResourceLenReturn.liveTracker out ready).global.protectedTags (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag
  have releasedNodes := congrArg BorrowTree.nodes releasedFrame
  have releasedRoots := congrArg BorrowTree.roots releasedFrame
  dsimp only at releasedNodes releasedRoots
  have namedNodes : (CurrentCallResourceLenReturn.releasedTree out ready).nodes=(CurrentCallResourceLenInvoke.borrowedTree out ready).nodes := by
    simpa only [CurrentCallResourceLenReturn.releasedTree] using releasedNodes
  have namedRoots : (CurrentCallResourceLenReturn.releasedTree out ready).roots=(CurrentCallResourceLenInvoke.borrowedTree out ready).roots := by
    simpa only [CurrentCallResourceLenReturn.releasedTree] using releasedRoots
  have finalAt : (CurrentCallResourceLenReturn.releasedTree out ready).nodes.get allocationRoot=some next:=by rw [namedNodes];exact nextAt
  have finalRoot : (CurrentCallResourceLenReturn.releasedTree out ready).roots[0]?=some allocationRoot:=by rw [namedRoots];exact rootSlot
  have rootTagEq : (CurrentCallResourceLenReturn.postTracker out ready).global.rootTag? id=out.boolOutput.global.rootTag? id:=rfl
  have lenEq : (sourceAllocation out ready).len=Q.allocation.len:=by
    have equal:=congrArg Allocation.len returned.sourceAllocation
    simpa only [sourceAllocation,CurrentCallResourceLenInvoke.entry,Allocation.setExtra,Allocation.mapExtra,Allocation.len] using equal.symm
  have byteSizeEq : (sourceAllocation out ready).byteSize=Q.allocation.byteSize:=by
    have equal:=congrArg Allocation.byteSize returned.sourceAllocation
    simpa only [sourceAllocation,CurrentCallResourceLenInvoke.entry,Allocation.setExtra,Allocation.mapExtra,Allocation.byteSize] using equal.symm
  have sharedTree : (child Q.allocation.extra out.boolOutput.global.protectedTags out.sourceOutput.tag out.boolOutput.global.nextPointerTag
      (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree=CurrentCallResourceSharedStage.tree out:=by rw [returned.sourceAllocation];rfl
  have sharedCapacity:=stage.capacity
  rw [sharedTree] at sharedCapacity
  refine ⟨present out ready returned,?_,?_,finalRoot,next,finalAt,nextParent.trans zeroParent,nextPermission.trans zeroDisabled,?_⟩
  · rw [lenEq,byteSizeEq]
    exact Q.issued.capability.extent
  · change (CurrentCallResourceLenReturn.releasedTree out ready).locations.size=(sourceAllocation out ready).byteSize
    rw [returned.capacity,sharedCapacity,byteSizeEq]
    exact Q.issued.capability.treeExtent
  · rw [nextTag]
    exact rootTagEq.trans zeroTag


theorem issued : SpatialDelegation returned.machine (CurrentCallResourceLenReturn.postTracker out ready) id
    (sourceAllocation out ready) returned.completion Q.pointer.grant := by
  apply issued_of_rootBelow (capability out ready returned)
  · simpa only [sourceAllocation,Allocation.setExtra,Allocation.mapExtra,CurrentCallResourceLenReturn.Result.completion] using returned.parents
  · exact returned.primaryBelow

end
end DuplicatePrefix.CurrentCallResourceLenCapability
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourceLenCapability.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual Len capability dependency {dependency}"
