import duplicate_prefix.CurrentCallResourceLenCapability

namespace DuplicatePrefix.CurrentCallResourceLenRoots
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

private def associated (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (room : global.nextPointerTag.value<18446744073709551615) (tag : BorTag) (offset len : UInt64) :=
  tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len) .Read
    (registered global {} allocation room).1.protectedTags .VisitChildrenOfAccessed

private def strongTree (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (room : global.nextPointerTag.value<18446744073709551615) (tag : BorTag) (offset len : UInt64) :=
  ((associated tree global allocation room tag offset len).tree.newChild (Size.ofBytes offset) (.concrete tag) global.nextPointerTag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree

private theorem helper_roots (tree : BorrowTree) (global : GlobalState) (completion : Completion)
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
 :
    (strongTree tree global allocation room readerNode.tag offset len).roots=tree.roots := by
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
  obtain ⟨_,_,metadata⟩:=GeneralBorrowSharedReadMetadata.construct accessed.tree registration.1 afterRuntime readerNode.tag global.nextPointerTag reader readerNode
    tagged readerAfter freshAfter nodeRoom true offset len nonzero currentBounds
  exact metadata.roots.trans roots

variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : Output limits C count) (ready : CurrentCallResourceBodyReadiness.Ready C)

private theorem stage_roots {nextData nextOwner}
    (Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut)
    (pointer : Q.pointer=CurrentCallResourceSourceAfterBool.pointer out)
    (allocation : Q.allocation=(CurrentCallResourceSourceFinal.entry out).allocation)
    (stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)) :
    (CurrentCallResourceSharedStage.tree out).roots=Q.allocation.extra.roots := by
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
  have roots:=leaf.roots.trans P.roots
  change (child Q.allocation.extra global.protectedTags out.sourceOutput.tag global.nextPointerTag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree.roots=Q.allocation.extra.roots at roots
  have treeEq : (child Q.allocation.extra global.protectedTags out.sourceOutput.tag global.nextPointerTag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree=
      CurrentCallResourceSharedStage.tree out:=by rw [allocation];rfl
  rw [treeEq] at roots
  exact roots

variable {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    (returned : CurrentCallResourceLenReturn.Result out ready Q stage)

include returned in
theorem roots : (CurrentCallResourceLenReturn.releasedTree out ready).roots=Q.allocation.extra.roots := by
  obtain ⟨snapshot⟩:=CurrentCallResourceLenReturn.preStrongSnapshot out ready Q returned.sourcePointer returned.sourceAllocation stage
  have nonzero : len≠0:=by intro zero;have positive:=C.positive;rw [zero] at positive;contradiction
  have helperRoots:=helper_roots
    (CurrentCallResourceSharedStage.tree out) (CurrentCallResourceLenInvoke.held out ready).global
    (extend Q.precise.completion stage.reader Q.pointer.grant) snapshot.runtime snapshot.parents snapshot.primarySlot snapshot.distinct
    Q.pointer.grant stage.reader snapshot.sourceNode snapshot.readerNode snapshot.sourceAt snapshot.readerAt snapshot.readerEdge snapshot.readerHidden snapshot.readerUnheld
    snapshot.primaryBelow id (CurrentCallResourceLenInvoke.helper_room out ready) (UInt64.ofNat offset) len nonzero snapshot.bounds snapshot.margin snapshot.readable snapshot.owned
  have actualTree : strongTree (CurrentCallResourceSharedStage.tree out) (CurrentCallResourceLenInvoke.held out ready).global id
      (CurrentCallResourceLenInvoke.helper_room out ready) snapshot.readerNode.tag (UInt64.ofNat offset) len=CurrentCallResourceLenInvoke.borrowedTree out ready := by
    rw [snapshot.readerTag]
    rfl
  rw [actualTree] at helperRoots
  have frame:=GeneralBorrowStructuralReleaseGeometryFrame.release (CurrentCallResourceLenInvoke.borrowedTree out ready)
    (CurrentCallResourceLenReturn.liveTracker out ready).global.protectedTags (CurrentCallResourceLenInvoke.held out ready).global.nextPointerTag
  have namedRoots : (CurrentCallResourceLenReturn.releasedTree out ready).roots=(CurrentCallResourceLenInvoke.borrowedTree out ready).roots := by
    simpa only [CurrentCallResourceLenReturn.releasedTree] using congrArg BorrowTree.roots frame
  exact namedRoots.trans (helperRoots.trans (stage_roots out ready Q returned.sourcePointer returned.sourceAllocation stage))

include returned in
theorem rootsDistinct : (CurrentCallResourceLenReturn.releasedTree out ready).roots.toList.Nodup := by
  have distinct : Q.allocation.extra.roots.toList.Nodup:=by rw [returned.sourceAllocation];exact CurrentCallResourceSourceFinal.roots out
  rw [←roots out ready returned] at distinct
  exact distinct

end
end DuplicatePrefix.CurrentCallResourceLenRoots
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourceLenRoots.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual resource AsMut call dependency {dependency}"
