import duplicate_prefix.CurrentCallResourceLenInvoke
import duplicate_prefix.CurrentCallResourceLenCaller
import duplicate_prefix.CurrentCallOptionalLenAssociatedRead
import duplicate_prefix.CurrentCallOptionalLenFuture
import duplicate_prefix.CurrentCallOptionalObserverRelease
import duplicate_prefix.LenReturnFromReleaseRuntime

namespace DuplicatePrefix.CurrentCallResourceLenReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallResourceEntryBody GeneralBorrowFnEntryRegistration GeneralBorrowRawSharedExpression
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder GeneralRangeMapOrigins
open S05ConcreteProtectedChildCompletion
open CanonicalConfigFacts ActualReferenceContext LenUncachedFrontend GeneralBorrowForestMixedLenBeforeReturn
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

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

private theorem transport_runtime (old next : BorrowTree) (oldGlobal nextGlobal : GlobalState)
    (treeEq : old=next) (globalEq : oldGlobal=nextGlobal)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts old oldGlobal) :
    DuplicatePrefixBorrowContract.RuntimeFacts next nextGlobal := by cases treeEq;cases globalEq;exact runtime

/-- A current unprotected reader and a saved q snapshot drive the actual Read,
protected constructor, release and single-frame endCall. q mutable authority
is retained only in the literal future view until that drop has happened. -/
private theorem release_current (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (parents : ParentInterpretation tree completion)
    (primarySlot : tree.roots[0]?=some allocationRoot) (distinct : tree.roots.toList.Nodup)
    (source reader : UniIndex) (sourceNode readerNode : TreeNode)
    (sourceAt : tree.nodes.get source=some sourceNode) (readerAt : tree.nodeAt reader=some readerNode)
    (readerEdge : readerNode.parent=some source) (readerHidden : readerNode.isExposed=false)
    (readerUnheld : global.protectedTags.contains readerNode.tag=false)
    (primaryBelow : Below completion allocationRoot source)
    (allocation : AllocId) (room : global.nextPointerTag.value<18446744073709551615)
    (offset len : UInt64) (nonzero : len≠0)
    (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat)
    (margin : tree.nodes.size+1<65536)
    (readable : OwnedOn (fun location => Nonempty (DuplicatePrefixNormalKind.Capability tree location global.protectedTags reader .Read))
      offset (offset+len) tree.locations)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags source)
      offset (offset+len) tree.locations) :
    let registration:=registered global {} allocation room
    let frame:=({} : FrameState).addProtector allocation global.nextPointerTag
    let actual:=strongTree tree global allocation room readerNode.tag offset len
    let released:=actual.releaseProtector global.nextPointerTag registration.1.protectedTags
    ∃ helper, actual.indexOfTag global.nextPointerTag=some helper ∧
      released.status=.Released ∧ DuplicatePrefixBorrowContract.RuntimeFacts released.tree (registration.1.endCall frame) ∧
      ParentInterpretation released.tree (extend completion helper reader) ∧ ParentTagOrder released.tree ∧
      released.tree.nodes.size<65536 ∧ released.tree.locations.size=tree.locations.size ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority released.tree (extend completion helper reader)
        (registration.1.endCall frame).protectedTags source) offset (offset+len) released.tree.locations ∧
      (∃ next,released.tree.nodes.get source=some next ∧ next.tag=sourceNode.tag ∧
        next.parent=sourceNode.parent ∧ next.isExposed=sourceNode.isExposed) ∧
      Below (extend completion helper reader) allocationRoot source ∧
      (∃ node,released.tree.nodes.get reader=some node ∧ node.tag=readerNode.tag ∧
        node.parent=some source ∧ node.isExposed=false ∧ registration.1.protectedTags.contains node.tag=false) ∧
      (∃ node,released.tree.nodes.get helper=some node ∧ node.tag=global.nextPointerTag ∧ node.parent=some reader ∧ node.isExposed=false) := by
  let registration:=registered global {} allocation room
  let frame:=({} : FrameState).addProtector allocation global.nextPointerTag
  let accessed:=associated tree global allocation room readerNode.tag offset len
  let actual:=strongTree tree global allocation room readerNode.tag offset len
  obtain ⟨position,root,rootNode,rootSlot,rootAt,sourcePath⟩:=CandidateCurrentWindowAuthority.root_path tree parents.graph source sourceNode sourceAt
  have readerPath : Path tree root reader:=.step sourcePath readerNode readerAt readerEdge
  obtain ⟨_,afterRuntime,afterParents,nodes,roots,tags,capacity,afterOwned⟩:=CurrentCallOptionalLenAssociatedRead.prepare tree global allocation completion runtime parents
    primarySlot distinct parents.order position root source reader rootNode readerNode primaryBelow rootSlot rootAt sourcePath readerAt readerPath readerEdge readerHidden readerUnheld
    room offset len bounds (by omega) readable owned
  change DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree registration.1 at afterRuntime
  change ParentInterpretation accessed.tree completion at afterParents
  change accessed.tree.nodes=tree.nodes at nodes
  change accessed.tree.roots=tree.roots at roots
  change accessed.tree.tagMapping=tree.tagMapping at tags
  change accessed.tree.locations.size=tree.locations.size at capacity
  obtain ⟨_,held,_,_,nodeFresh,fresh⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare tree global {} allocation room runtime
  have readerAfter : accessed.tree.nodeAt reader=some readerNode := by change accessed.tree.nodes.get _=_;rw [nodes];exact readerAt
  have sourceAfter : accessed.tree.nodes.get source=some sourceNode := by rw [nodes];exact sourceAt
  have tagged : accessed.tree.indexOfTag readerNode.tag=some reader:=afterRuntime.formed.allocator.nodeTags _ _ readerAfter
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [tags];exact fresh
  have nodeFreshAfter : GeneralBorrowProtector.Fresh accessed.tree global.nextPointerTag := by
    simpa only [GeneralBorrowProtector.Fresh,nodes] using nodeFresh
  have nodeRoom : accessed.tree.nodes.size+1≤4294967295 := by rw [nodes];omega
  have currentBounds : offset.toNat+len.toNat≤accessed.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have tagBound : global.nextPointerTag.value.toNat<registration.1.nextPointerTag.value.toNat := by
    have successor:=GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    change global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat
    omega
  have tagHeld : registration.1.protectedTags.contains global.nextPointerTag=true := by unfold ProtectedTags.contains;rw [held];rfl
  have futureOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority accessed.tree completion
      (registration.1.endCall frame).protectedTags source) offset (offset+len) accessed.tree.locations := by
    intro cursor valid positive start stop
    exact (afterOwned cursor valid positive start stop).2
  have afterReadable : OwnedOn (fun location=>Nonempty (DuplicatePrefixNormalKind.Capability accessed.tree location registration.1.protectedTags reader .Read))
      offset (offset+len) accessed.tree.locations := by
    intro cursor valid positive start stop
    exact (afterOwned cursor valid positive start stop).1
  obtain ⟨helper,lookup,futureAuthority⟩:=CurrentCallOptionalLenFuture.construct accessed.tree registration.1 completion afterRuntime afterParents allocation
    readerNode.tag global.nextPointerTag reader readerNode tagged readerAfter freshAfter nodeFreshAfter nodeRoom tagBound source ⟨sourceNode,sourceAfter⟩
    offset len nonzero currentBounds futureOwned
  obtain ⟨_,helperRuntime,helperCapacity,growth,other,otherLookup,caps⟩:=GeneralBorrowSharedReadConstructor.construct accessed.tree registration.1 afterRuntime
    readerNode.tag global.nextPointerTag reader readerNode tagged readerAfter freshAfter nodeRoom tagBound true tagHeld offset len nonzero currentBounds afterReadable
  have same : other=helper:=Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  change actual.locations.size=accessed.tree.locations.size at helperCapacity
  change actual.nodes.size≤accessed.tree.nodes.size+1 at growth
  obtain ⟨other,otherLookup,⟨helperNode,helperAt,helperTag,helperParent,helperHidden⟩,old⟩:=GeneralBorrowSharedChildGraph.construct accessed.tree registration.1 afterRuntime
    readerNode.tag global.nextPointerTag reader readerNode tagged readerAfter freshAfter nodeRoom true offset len nonzero currentBounds
  have same : other=helper:=Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  obtain ⟨nextReader,nextReaderAt,nextReaderTag,nextReaderParent,nextReaderHidden⟩:=old reader readerNode readerAfter
  obtain ⟨nextSource,nextSourceAt,nextSourceTag,nextSourceParent,nextSourceHidden⟩:=old source sourceNode sourceAfter
  let future:=registration.1.endCall frame
  have futureRuntime : DuplicatePrefixBorrowContract.RuntimeFacts accessed.tree future:=absent_runtime accessed.tree registration.1 afterRuntime allocation global.nextPointerTag
    (by intro index node present;exact nodeFreshAfter (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get accessed.tree.nodes index node).mpr present)))
  have unheld : future.protectedTags.contains global.nextPointerTag=false := by
    change (registration.1.protectedTags.remove global.nextPointerTag).contains global.nextPointerTag=false
    simp only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none]
  have heldEq:=shared_held_tree accessed.tree registration.1 afterRuntime readerNode.tag global.nextPointerTag reader readerNode tagged readerAfter freshAfter nodeRoom true false offset len nonzero currentBounds
  obtain ⟨_,_,_,_,other,otherLookup,leaf,_⟩:=CurrentCallSharedConstructorFrame.metadata accessed.tree future futureRuntime readerNode.tag global.nextPointerTag reader readerNode
    tagged readerAfter freshAfter nodeRoom tagBound unheld offset len nonzero currentBounds
  rw [←heldEq] at otherLookup leaf
  have same : other=helper:=Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  change LeafFrame accessed.tree actual helper reader at leaf
  have parentOrder : readerNode.tag.value≤global.nextPointerTag.value:=UInt64.le_of_lt
    (GeneralBorrowParentTagInvariant.parent_below_fresh tree global runtime reader readerNode readerAt)
  have helperOrder:=GeneralBorrowSharedChildParentTagOrder.construct accessed.tree registration.1 afterRuntime readerNode.tag global.nextPointerTag reader readerNode
    tagged readerAfter freshAfter nodeRoom true offset len nonzero currentBounds afterParents.order parentOrder
  have primaryAt : ∃ node,accessed.tree.nodes.get allocationRoot=some node:=by
    obtain ⟨node,present,_⟩:=parents.graph.rootNodes allocationRoot (Array.mem_toList_iff.mpr (Array.mem_of_getElem? primarySlot))
    exact ⟨node,by rw [nodes];exact present⟩
  have helperParents:=CurrentCallParentInsertion.of_leaf accessed.tree actual completion afterParents helper reader leaf primaryAt helperRuntime.formed.toGraphState helperOrder
  have helperPrimary : actual.roots[0]?=some allocationRoot := by rw [leaf.roots,roots];exact primarySlot
  have helperDistinct : actual.roots.toList.Nodup := by rw [leaf.roots,roots];exact distinct
  have sourcePrimary : Below (extend completion helper reader) allocationRoot source:=CurrentCallResourceChild.old_ancestry accessed.tree completion afterParents helper reader leaf.vacant primaryBelow
  obtain ⟨helperPosition,helperRoot,helperRootNode,helperRootSlot,helperRootAt,helperSourcePath⟩:=CandidateCurrentWindowAuthority.root_path actual helperParents.graph source nextSource nextSourceAt
  have nextReaderEdge : nextReader.parent=some source:=nextReaderParent.trans readerEdge
  have helperReaderPath : Path actual helperRoot helper:=.step (.step helperSourcePath nextReader nextReaderAt nextReaderEdge) helperNode helperAt helperParent
  obtain ⟨activityChild,activityLookup,activity⟩:=GeneralBorrowConstructorChildActivity.Shared.construct accessed.tree registration.1 afterRuntime
    readerNode.tag global.nextPointerTag reader readerNode tagged readerAfter freshAfter nodeRoom true offset len nonzero currentBounds
  have same : activityChild=helper:=Option.some.inj (activityLookup.symm.trans lookup)
  subst activityChild
  have initialPositive : offset.toNat<(offset+len).toNat := by
    have noWrap : offset.toNat+len.toNat<2^64:=Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt tree.locations.size.bytes)
    have lenPositive : 0<len.toNat:=Nat.pos_of_ne_zero (fun zero=>nonzero (UInt64.toNat_inj.mp zero))
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
    omega
  have nextUnheld : registration.1.protectedTags.contains nextReader.tag=false := by
    rw [nextReaderTag]
    have different : readerNode.tag≠global.nextPointerTag:=nodeFresh (reader,readerNode)
      (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes reader readerNode).mpr readerAt))
    exact (ProtectorInsertion.contains_other global.protectedTags global.nextPointerTag readerNode.tag .StrongProtector different).trans readerUnheld
  have releaseOwned : OwnedOn (fun location=>Nonempty (DuplicatePrefixNormalKind.Capability actual location registration.1.protectedTags helper .Read) ∧
      S05CompletedAncestryReadMutable.Authority actual (extend completion helper reader) future.protectedTags source location)
      offset (offset+len) actual.locations := by
    intro cursor valid positive start stop
    exact ⟨(caps cursor valid positive start stop).2,futureAuthority cursor valid positive start stop⟩
  have helperShort : actual.nodes.size<65536 := by rw [nodes] at growth;omega
  obtain ⟨done,releaseFrame,_,releasedParents,releasedCapacity,releasedOwned,releasedRuntime⟩:=CurrentCallOptionalObserverRelease.release actual registration.1 (extend completion helper reader)
    helperRuntime helperParents helperPrimary helperDistinct helperOrder helperPosition helperRoot source helper helperRootNode helperNode sourcePrimary helperRootSlot helperRootAt helperSourcePath
    helperAt helperReaderPath allocation reader nextReader helperParent nextReaderAt nextReaderEdge helperHidden (nextReaderHidden.trans readerHidden)
    offset len initialPositive activity frame (by simp only [frame,FrameState.addProtector,helperTag,Array.push_empty]) nextUnheld releaseOwned helperShort
  rw [helperTag] at done releaseFrame releasedParents releasedCapacity releasedOwned releasedRuntime
  refine ⟨helper,lookup,done,releasedRuntime,releasedParents,?_,?_,releasedCapacity.trans (helperCapacity.trans capacity),releasedOwned,
    ⟨nextSource,?_,nextSourceTag,nextSourceParent,nextSourceHidden⟩,sourcePrimary,
    ⟨nextReader,?_,nextReaderTag,nextReaderEdge,nextReaderHidden.trans readerHidden,nextUnheld⟩,
    ⟨helperNode,?_,helperTag,helperParent,helperHidden⟩⟩
  · rw [releaseFrame];exact helperOrder
  · rw [releaseFrame];exact helperShort
  · rw [releaseFrame];exact nextSourceAt
  · rw [releaseFrame];exact nextReaderAt
  · rw [releaseFrame];exact helperAt


variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : Output limits C count) (ready : CurrentCallResourceBodyReadiness.Ready C)

def liveTracker : MachineHooks.BorrowState := TypedBorrowSteps.registeredTracker
  (ReferenceBorrowDriver.allocatedTracker (CurrentCallResourceLenInvoke.held out ready)
    (CurrentCallResourceLenInvoke.helper_room out ready)) (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag

def helperFrame : FrameState := ({} : FrameState).addProtector id (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag

def releasedTree : BorrowTree := ((CurrentCallResourceLenInvoke.borrowedTree out ready).releaseProtector
  (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag (liveTracker out ready).global.protectedTags).tree

def postTracker : MachineHooks.BorrowState := {liveTracker out ready with global:=(liveTracker out ready).global.endCall (helperFrame out ready)}

/-- Derived resources at the actual unprotected-r phase, BEFORE the helper's
Strong tag is registered. No q mutable right under that Strong tag is claimed. -/
structure PreStrong {nextData nextOwner}
    (Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut)
    (stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)) where
  sourceNode : TreeNode
  sourceAt : (CurrentCallResourceSharedStage.tree out).nodes.get Q.pointer.grant=some sourceNode
  sourceTag : sourceNode.tag=out.sourceOutput.tag
  readerNode : TreeNode
  readerAt : (CurrentCallResourceSharedStage.tree out).nodeAt stage.reader=some readerNode
  readerTag : readerNode.tag=out.boolOutput.global.nextPointerTag
  readerEdge : readerNode.parent=some Q.pointer.grant
  readerHidden : readerNode.isExposed=false
  readerUnheld : (CurrentCallResourceLenInvoke.held out ready).global.protectedTags.contains readerNode.tag=false
  rootNode : TreeNode
  rootSlot : (CurrentCallResourceSharedStage.tree out).roots[stage.preparation.geometry.selectedPosition]?=some stage.preparation.geometry.selectedRoot
  rootAt : (CurrentCallResourceSharedStage.tree out).nodes.get stage.preparation.geometry.selectedRoot=some rootNode
  sourcePath : Path (CurrentCallResourceSharedStage.tree out) stage.preparation.geometry.selectedRoot Q.pointer.grant
  readerPath : Path (CurrentCallResourceSharedStage.tree out) stage.preparation.geometry.selectedRoot stage.reader
  primarySlot : (CurrentCallResourceSharedStage.tree out).roots[0]?=some allocationRoot
  primaryBelow : Below (extend Q.precise.completion stage.reader Q.pointer.grant) allocationRoot Q.pointer.grant
  distinct : (CurrentCallResourceSharedStage.tree out).roots.toList.Nodup
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallResourceSharedStage.tree out) (CurrentCallResourceLenInvoke.held out ready).global
  parents : ParentInterpretation (CurrentCallResourceSharedStage.tree out) (extend Q.precise.completion stage.reader Q.pointer.grant)
  margin : (CurrentCallResourceSharedStage.tree out).nodes.size+1<65536
  bounds : (UInt64.ofNat offset).toNat+len.toNat≤(CurrentCallResourceSharedStage.tree out).locations.size.bytes.toNat
  owned : OwnedOn (S05CompletedAncestryReadMutable.Authority (CurrentCallResourceSharedStage.tree out)
    (extend Q.precise.completion stage.reader Q.pointer.grant) (CurrentCallResourceLenInvoke.held out ready).global.protectedTags Q.pointer.grant)
    (UInt64.ofNat offset) (UInt64.ofNat offset+len) (CurrentCallResourceSharedStage.tree out).locations
  readable : OwnedOn (fun location=>Nonempty (DuplicatePrefixNormalKind.Capability (CurrentCallResourceSharedStage.tree out) location
    (CurrentCallResourceLenInvoke.held out ready).global.protectedTags stage.reader .Read))
    (UInt64.ofNat offset) (UInt64.ofNat offset+len) (CurrentCallResourceSharedStage.tree out).locations

/-- SAME Default-shared constructor supplies the q snapshot before helper
registration. No full q authority is assumed at the protected-h phase. -/
theorem preStrongSnapshot {nextData nextOwner}
    (Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut)
    (pointer : Q.pointer=CurrentCallResourceSourceAfterBool.pointer out)
    (allocation : Q.allocation=(CurrentCallResourceSourceFinal.entry out).allocation)
    (stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)) :
    Nonempty (PreStrong out ready Q stage) := by
  let global:=out.boolOutput.global
  let room:=CurrentCallResourceBodyReadiness.current_room out ready
  let P:=stage.preparation
  let accessed:=read Q.allocation.extra global.protectedTags out.sourceOutput.tag (UInt64.ofNat offset) len .VisitChildrenOfAccessed
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra global:=by rw [allocation];exact CurrentCallResourceSourceFinal.runtime out
  have distinct : Q.allocation.extra.roots.toList.Nodup:=by rw [allocation];exact CurrentCallResourceSourceFinal.roots out
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
  obtain ⟨_,_,_,_,reader,lookup,owned⟩:=CurrentCallDefaultSharedAuthority.construct accessed.tree (advanced global room) Q.precise.completion P.runtime P.parents
    out.sourceOutput.tag global.nextPointerTag Q.pointer.grant parent tagged parentAfter freshAfter roomAfter tagBound unheld
    (UInt64.ofNat offset) len nonzero boundsAfter P.owned
  have same : reader=stage.reader:=Option.some.inj (lookup.symm.trans stage.lookup)
  subst reader
  obtain ⟨reader,lookup,⟨readerNode,readerAt,readerTag,readerEdge,readerHidden⟩,old⟩:=GeneralBorrowSharedChildGraph.construct accessed.tree (advanced global room) P.runtime
    out.sourceOutput.tag global.nextPointerTag Q.pointer.grant parent tagged parentAfter freshAfter roomAfter false (UInt64.ofNat offset) len nonzero boundsAfter
  have same : reader=stage.reader:=Option.some.inj (lookup.symm.trans stage.lookup)
  subst reader
  obtain ⟨sourceNode,sourceAt,sourceTag,_,_⟩:=old Q.pointer.grant parent parentAfter
  obtain ⟨_,_,metadata⟩:=GeneralBorrowSharedReadMetadata.construct accessed.tree (advanced global room) P.runtime
    out.sourceOutput.tag global.nextPointerTag Q.pointer.grant parent tagged parentAfter freshAfter roomAfter false (UInt64.ofNat offset) len nonzero boundsAfter
  have treeEq : (child Q.allocation.extra global.protectedTags out.sourceOutput.tag global.nextPointerTag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree=
      CurrentCallResourceSharedStage.tree out:=by rw [allocation];rfl
  change (child Q.allocation.extra global.protectedTags out.sourceOutput.tag global.nextPointerTag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree.nodes.get stage.reader=some readerNode at readerAt
  change (child Q.allocation.extra global.protectedTags out.sourceOutput.tag global.nextPointerTag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree.nodes.get Q.pointer.grant=some sourceNode at sourceAt
  rw [treeEq] at readerAt sourceAt
  have roots : (CurrentCallResourceSharedStage.tree out).roots=Q.allocation.extra.roots:=by
    rw [←treeEq]
    exact metadata.roots.trans P.roots
  have primarySlot : (CurrentCallResourceSharedStage.tree out).roots[0]?=some allocationRoot:=by rw [roots];exact Q.issued.capability.rootSlot
  obtain ⟨rootNode,_,_,rootSlot,rootAt,_,_,sourcePath,readerPath,primary⟩:=CurrentCallResourceLenInvoke.stage_geometry Q runtime distinct
    out.sourceOutput.tag concrete room (UInt64.ofNat offset) len stage nodeRoom nonzero bounds
  rw [treeEq] at rootSlot rootAt sourcePath readerPath primary
  have selectedRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallResourceSharedStage.tree out) (CurrentCallResourceLenInvoke.held out ready).global:=by
    have known:=stage.runtime
    rw [treeEq] at known
    exact known
  have selectedParents : ParentInterpretation (CurrentCallResourceSharedStage.tree out) (extend Q.precise.completion stage.reader Q.pointer.grant):=by
    have known:=stage.parents
    rw [treeEq] at known
    exact known
  have margin : (CurrentCallResourceSharedStage.tree out).nodes.size+1<65536:=by
    have growth:=stage.growth
    rw [treeEq,allocation] at growth
    have initial:=CurrentCallResourceBodyReadiness.current_nodes out ready
    omega
  have currentBounds : (UInt64.ofNat offset).toNat+len.toNat≤(CurrentCallResourceSharedStage.tree out).locations.size.bytes.toNat:=by
    have cap:=stage.capacity
    rw [treeEq] at cap
    rw [cap]
    exact bounds
  have actualOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority (CurrentCallResourceSharedStage.tree out)
      (extend Q.precise.completion stage.reader Q.pointer.grant) (CurrentCallResourceLenInvoke.held out ready).global.protectedTags Q.pointer.grant)
      (UInt64.ofNat offset) (UInt64.ofNat offset+len) (CurrentCallResourceSharedStage.tree out).locations:=by
    change OwnedOn (S05CompletedAncestryReadMutable.Authority
      (child Q.allocation.extra global.protectedTags out.sourceOutput.tag global.nextPointerTag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree
      (extend Q.precise.completion stage.reader Q.pointer.grant) (advanced global room).protectedTags Q.pointer.grant)
      (UInt64.ofNat offset) (UInt64.ofNat offset+len)
      (child Q.allocation.extra global.protectedTags out.sourceOutput.tag global.nextPointerTag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree.locations at owned
    rw [treeEq] at owned
    exact owned
  have readable : OwnedOn (fun location=>Nonempty (DuplicatePrefixNormalKind.Capability (CurrentCallResourceSharedStage.tree out) location
      (CurrentCallResourceLenInvoke.held out ready).global.protectedTags stage.reader .Read))
      (UInt64.ofNat offset) (UInt64.ofNat offset+len) (CurrentCallResourceSharedStage.tree out).locations:=by
    have caps:=stage.capabilities
    rw [treeEq] at caps
    intro cursor valid positive start stop
    exact (caps cursor valid positive start stop).2
  refine ⟨⟨sourceNode,sourceAt,sourceTag.trans binding.2.symm,readerNode,readerAt,readerTag,readerEdge,readerHidden,?_,
    rootNode,rootSlot,rootAt,sourcePath,readerPath,primarySlot,primary allocationRoot primarySlot,?_,selectedRuntime,selectedParents,margin,currentBounds,actualOwned,readable⟩⟩
  · rw [readerTag]
    exact unheld
  · rw [roots];exact distinct

structure Dropped {nextData nextOwner}
    (Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut)
    (stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)) where
  helperIndex : UniIndex
  lookup : (CurrentCallResourceLenInvoke.borrowedTree out ready).indexOfTag (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag=some helperIndex
  status : ((CurrentCallResourceLenInvoke.borrowedTree out ready).releaseProtector
    (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag (liveTracker out ready).global.protectedTags).status=.Released
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts (releasedTree out ready) (postTracker out ready).global
  parents : ParentInterpretation (releasedTree out ready) (extend (extend Q.precise.completion stage.reader Q.pointer.grant) helperIndex stage.reader)
  order : ParentTagOrder (releasedTree out ready)
  short : (releasedTree out ready).nodes.size<65536
  capacity : (releasedTree out ready).locations.size=(CurrentCallResourceSharedStage.tree out).locations.size
  owned : OwnedOn (S05CompletedAncestryReadMutable.Authority (releasedTree out ready)
    (extend (extend Q.precise.completion stage.reader Q.pointer.grant) helperIndex stage.reader)
    (postTracker out ready).global.protectedTags Q.pointer.grant) (UInt64.ofNat offset) (UInt64.ofNat offset+len) (releasedTree out ready).locations
  primaryBelow : Below (extend (extend Q.precise.completion stage.reader Q.pointer.grant) helperIndex stage.reader) allocationRoot Q.pointer.grant
  sourceNode : TreeNode
  sourceAt : (releasedTree out ready).nodes.get Q.pointer.grant=some sourceNode
  sourceTag : sourceNode.tag=out.sourceOutput.tag
  readerNode : TreeNode
  readerAt : (releasedTree out ready).nodes.get stage.reader=some readerNode
  readerTag : readerNode.tag=out.boolOutput.global.nextPointerTag
  readerEdge : readerNode.parent=some Q.pointer.grant
  readerHidden : readerNode.isExposed=false
  readerUnheld : (liveTracker out ready).global.protectedTags.contains readerNode.tag=false
  helperNode : TreeNode
  helperAt : (releasedTree out ready).nodes.get helperIndex=some helperNode
  helperTag : helperNode.tag=(CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag
  helperEdge : helperNode.parent=some stage.reader
  helperHidden : helperNode.isExposed=false

/-- The SAME pre-Strong snapshot derives the actual helper release and restored q rights. -/
theorem drop {nextData nextOwner}
    (Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut)
    (pointer : Q.pointer=CurrentCallResourceSourceAfterBool.pointer out)
    (allocation : Q.allocation=(CurrentCallResourceSourceFinal.entry out).allocation)
    (stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)) :
    Nonempty (Dropped out ready Q stage) := by
  obtain ⟨snapshot⟩:=preStrongSnapshot out ready Q pointer allocation stage
  have nonzero : len≠0:=by intro zero;have p:=C.positive;rw [zero] at p;contradiction
  obtain ⟨helper,lookup,status,runtime,parents,order,short,capacity,owned,⟨sourceNode,sourceAt,sourceTag,_,_⟩,
    primaryBelow,⟨readerNode,readerAt,readerTag,readerEdge,readerHidden,readerUnheld⟩,
    ⟨helperNode,helperAt,helperTag,helperEdge,helperHidden⟩⟩:=release_current
    (CurrentCallResourceSharedStage.tree out) (CurrentCallResourceLenInvoke.held out ready).global
    (extend Q.precise.completion stage.reader Q.pointer.grant) snapshot.runtime snapshot.parents snapshot.primarySlot snapshot.distinct
    Q.pointer.grant stage.reader snapshot.sourceNode snapshot.readerNode snapshot.sourceAt snapshot.readerAt snapshot.readerEdge snapshot.readerHidden snapshot.readerUnheld
    snapshot.primaryBelow id (CurrentCallResourceLenInvoke.helper_room out ready) (UInt64.ofNat offset) len nonzero snapshot.bounds snapshot.margin snapshot.readable snapshot.owned
  have actualTree : strongTree (CurrentCallResourceSharedStage.tree out) (CurrentCallResourceLenInvoke.held out ready).global id
      (CurrentCallResourceLenInvoke.helper_room out ready) snapshot.readerNode.tag (UInt64.ofNat offset) len=CurrentCallResourceLenInvoke.borrowedTree out ready := by
    rw [snapshot.readerTag]
    rfl
  let registration:=registered (CurrentCallResourceLenInvoke.held out ready).global {} id (CurrentCallResourceLenInvoke.helper_room out ready)
  let raw:=strongTree (CurrentCallResourceSharedStage.tree out) (CurrentCallResourceLenInvoke.held out ready).global id
    (CurrentCallResourceLenInvoke.helper_room out ready) snapshot.readerNode.tag (UInt64.ofNat offset) len
  let oldRelease:=raw.releaseProtector (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag registration.1.protectedTags
  let nextRelease:=(CurrentCallResourceLenInvoke.borrowedTree out ready).releaseProtector
    (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag (liveTracker out ready).global.protectedTags
  have releaseFlags : registration.1.protectedTags=(liveTracker out ready).global.protectedTags:=rfl
  have releaseEq : oldRelease=nextRelease :=
    (congrArg (fun tree : BorrowTree=>tree.releaseProtector (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag registration.1.protectedTags) actualTree).trans
      (congrArg (fun flags : ProtectedTags=>(CurrentCallResourceLenInvoke.borrowedTree out ready).releaseProtector (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag flags) releaseFlags)
  have releasedEq : oldRelease.tree=releasedTree out ready:=congrArg BorrowTree.ProtectorReleaseResult.tree releaseEq
  have futureGlobal : registration.1.endCall (helperFrame out ready)=(postTracker out ready).global:=rfl
  have actualRuntime:=transport_runtime oldRelease.tree (releasedTree out ready) (registration.1.endCall (helperFrame out ready)) (postTracker out ready).global releasedEq futureGlobal runtime
  have actualParents : ParentInterpretation (releasedTree out ready) (extend (extend Q.precise.completion stage.reader Q.pointer.grant) helper stage.reader):=
    Eq.mp (congrArg (fun tree=>ParentInterpretation tree (extend (extend Q.precise.completion stage.reader Q.pointer.grant) helper stage.reader)) releasedEq) parents
  have actualOrder : ParentTagOrder (releasedTree out ready):=Eq.mp (congrArg ParentTagOrder releasedEq) order
  have actualShort := short
  have releasedNodes := congrArg BorrowTree.nodes releasedEq
  dsimp only [oldRelease,raw,registration] at releasedNodes
  rw [releasedNodes] at actualShort
  have actualCapacity := capacity
  have releasedCapacity := congrArg (fun tree : BorrowTree=>tree.locations.size) releasedEq
  dsimp only [oldRelease,raw,registration] at releasedCapacity
  rw [releasedCapacity] at actualCapacity
  have actualOwned := owned
  have literalTreeEq := releasedEq
  dsimp only [oldRelease,raw,registration] at literalTreeEq
  rw [literalTreeEq] at actualOwned
  have futureFlags := congrArg GlobalState.protectedTags futureGlobal
  dsimp only [registration,helperFrame] at futureFlags
  rw [futureFlags] at actualOwned
  have actualLookup : (CurrentCallResourceLenInvoke.borrowedTree out ready).indexOfTag (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag=some helper:=
    (congrArg (fun tree=>tree.indexOfTag (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag) actualTree).symm.trans lookup
  have actualStatus : nextRelease.status=.Released:=(congrArg BorrowTree.ProtectorReleaseResult.status releaseEq).symm.trans status
  have actualSourceAt := sourceAt
  have actualReaderAt := readerAt
  have actualHelperAt := helperAt
  rw [literalTreeEq] at actualSourceAt actualReaderAt actualHelperAt
  have actualReaderUnheld : (liveTracker out ready).global.protectedTags.contains readerNode.tag=false:=by rw [←releaseFlags];exact readerUnheld
  exact ⟨⟨helper,actualLookup,actualStatus,actualRuntime,actualParents,actualOrder,actualShort,actualCapacity,actualOwned,primaryBelow,
    sourceNode,actualSourceAt,sourceTag.trans snapshot.sourceTag,readerNode,actualReaderAt,readerTag.trans snapshot.readerTag,readerEdge,readerHidden,actualReaderUnheld,
    helperNode,actualHelperAt,helperTag,helperEdge,helperHidden⟩⟩

private theorem caller_size (frame : CompilerFrameContext.ActualFrame)
    (shape : GenericFunctionEntryPrefix.Shape (CurrentCallResourceEntry.finishedFrame out) frame count) (base : UInt64) :
    (CurrentCallResourceLenInvoke.sharedFrame out frame shape base).locals.size=25 := by
  simpa only [CurrentCallResourceLenInvoke.sharedFrame,CurrentCallResourceSharedStage.afterFrame,CopyHelperSteps.advance,
    ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set] using shape.size

structure Result {nextData nextOwner}
    (Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut)
    (stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready))
    extends Dropped out ready Q stage where
  callerFrame : CompilerFrameContext.ActualFrame
  shape : GenericFunctionEntryPrefix.Shape (CurrentCallResourceEntry.finishedFrame out) callerFrame count
  sourcePointer : Q.pointer=CurrentCallResourceSourceAfterBool.pointer out
  sourceAllocation : Q.allocation=(CurrentCallResourceSourceFinal.entry out).allocation
  sourceCompletion : Q.precise.completion=CurrentCallResourceSourceFinal.completion out
  base : UInt64
  helper : CurrentCallResourceLenInvoke.Returned out ready callerFrame shape base
  rootFrame : CompilerFrameContext.ActualFrame
  machine : Before
  trace : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
    (Storage.withCurrent #[] (CurrentCallResourceEntry.finishedFrame out) out.finalMachine) (Storage.withCurrent #[] rootFrame machine)
  rootEq : rootFrame={PtrMetadataExecution.writeFrame
    (cachedCaller (CurrentCallResourceLenInvoke.sharedFrame out callerFrame shape base) (by rw [caller_size out callerFrame shape base];decide))
    11 (.scalar (.fromScalarInt (.ofUInt64 len))) (by simp only [cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set];rw [caller_size out callerFrame shape base];decide)
      with location:=.mir ⟨3,0⟩}
  memory : machine.memory=RetagEntry.updatedMemory (CurrentCallResourceSharedStage.afterMachine out ready).memory id
    (CurrentCallResourceLenInvoke.entry out) (releasedTree out ready)
  tracked : machine.borrowTracker=some (postTracker out ready)
  flags : GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span helper.machine machine
  active : ∃ thread,machine.threads.activeThread?=some thread ∧ thread.topUserRelevantFrame=some 0
  sourceLive : machine.memory.live.find? (fun row=>row.1==id)=some
    (id,{(CurrentCallResourceLenInvoke.entry out) with allocation := (CurrentCallResourceLenInvoke.entry out).allocation.setExtra (releasedTree out ready)})

namespace Result
variable {out ready nextData nextOwner}
  {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
  {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
  (result : Result out ready Q stage)

def source (_result : Result out ready Q stage) := Q
def sharedStage (_result : Result out ready Q stage) := stage
def completion : Completion := extend (extend Q.precise.completion stage.reader Q.pointer.grant) result.helperIndex stage.reader

theorem completionEq : result.completion=extend (extend Q.precise.completion stage.reader Q.pointer.grant) result.helperIndex stage.reader:=rfl

theorem helperLookup : (CurrentCallResourceLenInvoke.borrowedTree out ready).indexOfTag
    (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag=some result.helperIndex:=result.lookup

end Result

private theorem released_pair (result : BorrowTree.ProtectorReleaseResult)
    (done : result.status=.Released) : result=⟨result.tree,.Released⟩ := by
  cases result
  cases done
  rfl

private theorem caller_local (caller : CompilerFrameContext.ActualFrame)
    (size : caller.locals.size=25)
    (slot : caller.locals[11]?=some ⟨.live (.immediate .uninit),some RootCompilerFacts.usizeLayout⟩) :
    ∃ valid : (11 : MIR.LocalId)<caller.locals.size,
      caller.locals[11].value=.live (.immediate .uninit) ∧ caller.locals[11].layout=some RootCompilerFacts.usizeLayout := by
  have valid : (11 : MIR.LocalId)<caller.locals.size := by rw [size];decide
  have cell := Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans slot)
  exact ⟨valid,congrArg LocalState.value cell,congrArg LocalState.layout cell⟩

/-- Execute the actual Len helper body, release its single Strong protector,
and pop to the SAME caller at root3 with the length in local11. -/
theorem invoke (stackReady : CurrentCallPush.StackReadiness before #[])
    (budget : Nat) (dispatch : limits.callDispatch=budget+1) (nonzero : count≠0) :
    ∃ nextData nextOwner,
      ∃ Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut,
      ∃ stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready),
      Nonempty (Result out ready Q stage) := by
  obtain ⟨frame,nextData,nextOwner,Q,shape,stage,base,helper,pointer,allocation,completion,trace⟩ :=
    CurrentCallResourceLenInvoke.invoke out ready stackReady budget dispatch nonzero
  obtain ⟨dropped⟩ := drop out ready Q pointer allocation stage
  have validShared : 11<(CurrentCallResourceLenInvoke.sharedFrame out frame shape base).locals.size := by
    rw [caller_size out frame shape base];decide
  let caller := cachedCaller (CurrentCallResourceLenInvoke.sharedFrame out frame shape base) validShared
  obtain ⟨size,slot,callerRace⟩ := CurrentCallResourceLenCaller.facts out frame shape base validShared
  obtain ⟨valid,live,cached⟩ := caller_local caller size slot
  have frameOwned : (helperFrame out ready).protectedTags=#[(id,(CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag)] := by
    simp [helperFrame,FrameState.addProtector]
  have complete : (CurrentCallResourceLenInvoke.borrowedTree out ready).releaseProtector
      (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag (liveTracker out ready).global.protectedTags=
      ⟨releasedTree out ready,.Released⟩ := released_pair _ dropped.status
  obtain ⟨rootFrame,machine,step,rootEq,memory,tracked,flags,active⟩ := LenReturnFromReleaseRuntime.step
    options limits remaining span C.model.debugOff C.validationFuel C.validationEq #[] caller helper.helper helper.machine len
    _ helper.facts helper.location helper.returned helper.clocks helper.destination helper.continuation helper.varargs
    valid live cached callerRace id (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag
    (CurrentCallResourceLenInvoke.entry out) (CurrentCallResourceLenInvoke.borrowedTree out ready) (releasedTree out ready)
    (CurrentCallResourceSharedStage.afterMachine out ready).memory helper.memory (liveTracker out ready) (helperFrame out ready)
    helper.tracked helper.protector frameOwned complete helper.cache helper.race helper.ghost helper.shallow
  have sourceLive : machine.memory.live.find? (fun row=>row.1==id)=some
      (id,{(CurrentCallResourceLenInvoke.entry out) with allocation:=(CurrentCallResourceLenInvoke.entry out).allocation.setExtra (releasedTree out ready)}) := by
    rw [memory]
    exact StackPopRelease.lookup_commit_same _ _ _ _
  refine ⟨nextData,nextOwner,Q,stage,⟨{
    toDropped := dropped
    callerFrame := frame
    shape := shape
    sourcePointer := pointer
    sourceAllocation := allocation
    sourceCompletion := completion
    base := base
    helper := helper
    rootFrame := rootFrame
    machine := machine
    trace := ?_
    rootEq := rootEq
    memory := memory
    tracked := tracked
    flags := flags
    active := active rfl
    sourceLive := sourceLive }⟩⟩
  exact SuccessfulTrace.append trace (.next step (.refl _))

end
end DuplicatePrefix.CurrentCallResourceLenReturn
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourceLenReturn.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual uniform Len return dependency {dependency}"
