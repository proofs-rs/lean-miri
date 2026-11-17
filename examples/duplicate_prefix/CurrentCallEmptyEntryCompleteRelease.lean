import duplicate_prefix.CurrentCallEntryProtectionData
import duplicate_prefix.S05CurrentMutableProtectorRelease
import duplicate_prefix.S05CompletedChildReanchor
namespace DuplicatePrefix.CurrentCallEmptyEntryCompleteRelease
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall GeneralRangeMapOrigins GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder GeneralBorrowFnEntryRegistration GeneralBorrowFreshActiveWithin
open S05CompletedAncestryReadMutable (Authority)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def written (output : GeneralBorrowForestFnEntry.Output) (offset : UInt64) :=
  output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes offset) (Size.ofBytes 1)
    .Write output.global.protectedTags .VisitChildrenOfAccessed

def released (output : GeneralBorrowForestFnEntry.Output) (offset : UInt64) :=
  (written output offset).tree.releaseProtector output.tag output.global.protectedTags

/-- Derived operation data, consumed internally by empty-entry return proofs. -/
structure Result (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (pointer : PointerInstance) (offset : UInt64)
    (room : global.nextPointerTag.value < 18446744073709551615) where
  output : GeneralBorrowForestFnEntry.Output
  actual : CandidateCurrentFnEntryRaw.operation tree global frame allocation pointer.value.provenance offset 1 = .ok output
  tag : output.tag = global.nextPointerTag
  globalEq : output.global = (registered global frame allocation room).1
  frameEq : output.frame = frame.addProtector allocation global.nextPointerTag
  readCompleted : output.access.status = .Completed
  childCompleted : output.child.outcome = .ok ()
  child : UniIndex
  lookup : output.child.tree.indexOfTag output.tag = some child
  node : TreeNode
  childAt : output.child.tree.nodeAt child = some node
  nodeTag : node.tag = output.tag
  leaf : node.children = #[]
  hidden : node.isExposed = false
  metadata : CandidateCurrentFnEntryRaw.Metadata tree output.child.tree
  childComplete : Completes output.child.tree (S05ConcreteProtectedChildCompletion.extend completion child pointer.grant)
  writeCompleted : (written output offset).status = .Completed
  writeRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (written output offset).tree output.global
  writeComplete : Completes (written output offset).tree (S05ConcreteProtectedChildCompletion.extend completion child pointer.grant)
  writeOrder : ParentTagOrder (written output offset).tree
  writeNodes : (written output offset).tree.nodes = output.child.tree.nodes
  writeCapacity : (written output offset).tree.locations.size = tree.locations.size
  writeActive : ActiveWithin (written output offset).tree child .Write offset (offset+1)
  writeOwned : OwnedOn (Authority (written output offset).tree (S05ConcreteProtectedChildCompletion.extend completion child pointer.grant)
    output.global.protectedTags child) offset (offset+1) (written output offset).tree.locations
  releaseCompleted : (released output offset).status = .Released
  releaseRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (released output offset).tree output.global
  releaseComplete : Completes (released output offset).tree (S05ConcreteProtectedChildCompletion.extend completion child pointer.grant)
  releaseOrder : ParentTagOrder (released output offset).tree
  releaseShape : (released output offset).tree = {(written output offset).tree with locations := (released output offset).tree.locations}
  releaseCapacity : (released output offset).tree.locations.size = tree.locations.size
  releaseNode : (released output offset).tree.nodeAt child = some node
  releaseOwned : OwnedOn (Authority (released output offset).tree (S05ConcreteProtectedChildCompletion.extend completion child pointer.grant)
    output.global.protectedTags child) offset (offset+1) (released output offset).tree.locations
  originalNode : TreeNode
  originalPresent : (released output offset).tree.nodeAt pointer.grant = some originalNode
  originalProvenance : match pointer.value.provenance with
    | .concrete _ tag => tag=originalNode.tag | .wildcard => originalNode.isExposed=true
  originalOwned : OwnedOn (Authority (released output offset).tree (S05ConcreteProtectedChildCompletion.extend completion child pointer.grant)
    (output.global.endCall output.frame).protectedTags pointer.grant) offset (offset+1) (released output offset).tree.locations
  originalNormal : OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal (released output offset).tree location
    (output.global.endCall output.frame).protectedTags pointer.grant)) offset (offset+1) (released output offset).tree.locations
  afterRuntime : S04ReturnReleaseParent.HiddenFrame (released output offset).tree output.frame →
    DuplicatePrefixBorrowContract.RuntimeFacts (released output offset).tree (output.global.endCall output.frame)

private theorem prepared_read (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (pointer : PointerInstance) (node : TreeNode) (present : tree.nodes.get pointer.grant = some node)
    (provenance : match pointer.value.provenance with | .concrete _ tag => tag=node.tag | .wildcard => node.isExposed=true)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (short : tree.nodes.size < 65536) (offset : UInt64) (bounds : offset.toNat+1 ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags pointer.grant) offset (offset+1) tree.locations) :
    let output := CurrentCallTypedFnEntry.literal tree global frame allocation room pointer.value.provenance offset 1
    DuplicatePrefixBorrowContract.RuntimeFacts output.access.tree output.global ∧
      Completes output.access.tree completion ∧ output.access.tree.nodes=tree.nodes ∧
      output.access.tree.tagMapping=tree.tagMapping ∧ output.access.tree.locations.size=tree.locations.size := by
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path tree runtime.formed.toGraphState pointer.grant node present
  cases prov : pointer.value.provenance with
  | concrete id tag =>
    have tagEq : tag=node.tag := by simpa only [prov] using provenance
    obtain ⟨_,afterRuntime,afterComplete,_,nodes,_,tags,capacity⟩ := S05ConcreteFnEntryRaw.prepare_read tree global frame allocation completion runtime complete order
      position root pointer.grant rootNode node slot rootAt present path room offset 1 bounds owned short .VisitChildrenOfAccessed
    simpa only [CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov,tagEq]
      using And.intro afterRuntime (And.intro afterComplete (And.intro nodes (And.intro tags capacity)))
  | wildcard =>
    have exposed : node.isExposed=true := by simpa only [prov] using provenance
    obtain ⟨_,afterRuntime,afterComplete,_,nodes,_,tags,capacity⟩ := S05WildcardFnEntryRaw.prepare_read tree global frame allocation completion runtime complete order
      position root pointer.grant rootNode node slot rootAt present exposed path room offset 1 bounds owned short .VisitChildrenOfAccessed
    simpa only [CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov]
      using And.intro afterRuntime (And.intro afterComplete (And.intro nodes (And.intro tags capacity)))

private theorem child_data (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (pointer : PointerInstance) (node : TreeNode) (sourcePresent : tree.nodes.get pointer.grant=some node)
    (provenance : match pointer.value.provenance with | .concrete _ tag => tag=node.tag | .wildcard => node.isExposed=true)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size < 65536)
    (offset : UInt64) (bounds : offset.toNat+1 ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags pointer.grant) offset (offset+1) tree.locations)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation tree global frame allocation pointer.value.provenance offset 1=.ok output)
    (outputTag : output.tag=global.nextPointerTag) (child : UniIndex)
    (lookup : output.child.tree.indexOfTag output.tag=some child) :
    ∃ node, output.child.tree.nodes.get child=some node ∧ node.tag=output.tag ∧ node.children=#[] ∧ node.isExposed=false ∧
      ActiveWithin output.child.tree child .Write offset (offset+1) := by
  let literal := CurrentCallTypedFnEntry.literal tree global frame allocation room pointer.value.provenance offset 1
  have outputEq : output=literal := Except.ok.inj (actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  obtain ⟨readRuntime,readComplete,readNodes,readTags,readCapacity⟩ := prepared_read tree global frame allocation completion runtime complete order
    pointer node sourcePresent provenance room short offset bounds owned
  change DuplicatePrefixBorrowContract.RuntimeFacts literal.access.tree literal.global at readRuntime
  change Completes literal.access.tree completion at readComplete
  change literal.access.tree.nodes=tree.nodes at readNodes
  change literal.access.tree.tagMapping=tree.tagMapping at readTags
  change literal.access.tree.locations.size=tree.locations.size at readCapacity
  obtain ⟨_,held,_,_,_,originalFresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation room runtime
  have fresh : GeneralBorrowTagMap.Fresh literal.access.tree.tagMapping global.nextPointerTag := by
    rw [readTags];exact originalFresh
  have currentRoom : literal.access.tree.nodes.size+1 ≤ 4294967295 := by rw [readNodes];exact nodeRoom
  have nodeAt : literal.access.tree.nodes.get pointer.grant = some node := by rw [readNodes];exact sourcePresent
  have bounds : offset.toNat+1 ≤ literal.access.tree.locations.size.bytes.toNat := by
    rw [readCapacity];exact bounds
  have own : literal.child.tree.indexOfTag global.nextPointerTag = some child := by
    simpa only [outputTag] using (show literal.child.tree.indexOfTag output.tag = some child from by rw [←outputEq];exact lookup)
  cases prov : pointer.value.provenance with
  | concrete id tag =>
    have tagged : literal.access.tree.indexOfTag tag = some pointer.grant := by
      have tagEq : tag = node.tag := by simpa [prov] using provenance
      rw [tagEq]
      exact (readComplete.2.2.2.2.1 pointer.grant node nodeAt).1
    obtain ⟨freshChild,node,lookup,found,nodeTag,leaf,hidden,activity⟩ := CurrentCallEntryProtectionData.concrete_constructor literal.access.tree literal.global
      readRuntime tag global.nextPointerTag pointer.grant node tagged nodeAt fresh currentRoom
      offset 1 (by decide) bounds
    have lookup' : literal.child.tree.indexOfTag global.nextPointerTag = some freshChild := by
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshMetadataChildMutableSlot.result,
        GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using lookup
    have same : freshChild = child := Option.some.inj (lookup'.symm.trans own)
    subst freshChild
    refine ⟨node,?_,?_,leaf,hidden,?_⟩
    · rw [outputEq]
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshMetadataChildMutableSlot.result,
        GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using found
    · rw [outputTag]
      exact nodeTag
    · rw [outputEq]
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using activity
  | wildcard =>
    obtain ⟨freshChild,node,lookup,found,nodeTag,leaf,hidden,activity⟩ := CurrentCallEntryProtectionData.wildcard_constructor
      literal.access.tree literal.global readRuntime global.nextPointerTag fresh currentRoom
      offset 1 (by decide) bounds
    have lookup' : literal.child.tree.indexOfTag global.nextPointerTag = some freshChild := by
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using lookup
    have same : freshChild = child := Option.some.inj (lookup'.symm.trans own)
    subst freshChild
    refine ⟨node,?_,?_,leaf,hidden,?_⟩
    · rw [outputEq]
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using found
    · rw [outputTag]
      exact nodeTag
    · rw [outputEq]
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using activity


/-- Actual Bool FnEntry, activating Write and protector release from one current
completion. Whole-frame bookkeeping is retained as a future flags expression. -/
theorem construct (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (pointer : PointerInstance) (sourceNode : TreeNode) (present : tree.nodes.get pointer.grant=some sourceNode)
    (provenance : match pointer.value.provenance with | .concrete _ tag => tag=sourceNode.tag | .wildcard => sourceNode.isExposed=true)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size+1 < 65536)
    (offset : UInt64) (bounds : offset.toNat+1 ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags pointer.grant) offset (offset+1) tree.locations) :
    Nonempty (Result tree global frame allocation completion pointer offset room) := by
  obtain ⟨output,actual,tag,globalEq,readDone,childDone,childRuntime,child,lookup,childComplete,childOwned,metadata,childWitness⟩ :=
    CandidateCurrentFnEntryRaw.source_only tree global frame allocation completion runtime complete order pointer sourceNode present provenance
      room nodeRoom (by omega) offset 1 (by decide) bounds owned
  have outputEq : output=CurrentCallTypedFnEntry.literal tree global frame allocation room pointer.value.provenance offset 1 :=
    Except.ok.inj (actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  have frameEq : output.frame=frame.addProtector allocation global.nextPointerTag := by rw [outputEq];rfl
  obtain ⟨node,childAt,nodeTag,leaf,hidden,active⟩ := child_data tree global frame allocation completion runtime complete order
    pointer sourceNode present provenance room nodeRoom (by omega) offset bounds owned output actual tag child lookup
  let extended := S05ConcreteProtectedChildCompletion.extend completion child pointer.grant
  have afterBounds : offset.toNat+1 ≤ output.child.tree.locations.size.bytes.toNat := by rw [metadata.capacity];exact bounds
  have afterShort : output.child.tree.nodes.size<65536 := Nat.lt_of_le_of_lt metadata.growth short
  have vacuous : OwnedOn (Authority output.child.tree extended output.global.protectedTags child) 0 0 output.child.tree.locations := by
    intro cursor valid impossible;omega
  obtain ⟨writeDone,writeRuntime,writeComplete,writeNodes,writeCapacity,_⟩ := CurrentCallBoolProtection.write_range
    output.child.tree output.global extended childRuntime childComplete metadata.order child node childAt offset afterBounds afterShort
    childOwned child 0 0 (by intro point lower upper;omega) vacuous
  have writeOwned := CurrentCallEntryProtectionData.write_authority output.child.tree output.global extended childRuntime childComplete
    metadata.order child node childAt offset afterBounds afterShort childOwned
  have writeActive := GeneralBorrowFreshActiveWithinAccess.normal output.child.tree node.tag (Size.ofBytes offset) (Size.ofBytes 1)
    .Write output.global.protectedTags .VisitChildrenOfAccessed child offset (offset+1) childRuntime.formed.well afterBounds
    (Nat.le_refl _) (Nat.le_refl _) active
  rw [nodeTag] at writeDone writeRuntime writeComplete writeNodes writeCapacity writeOwned writeActive
  change (written output offset).status=.Completed at writeDone
  change DuplicatePrefixBorrowContract.RuntimeFacts (written output offset).tree output.global at writeRuntime
  change Completes (written output offset).tree extended at writeComplete
  change (written output offset).tree.nodes=output.child.tree.nodes at writeNodes
  have writeOrder := GeneralBorrowParentTagInvariant.nodes_frame output.child.tree (written output offset).tree writeNodes metadata.order
  have writtenAt : (written output offset).tree.nodeAt child=some node := by change (written output offset).tree.nodes.get child=_;rw [writeNodes];exact childAt
  have writtenShort : (written output offset).tree.nodes.size<65536 := by rw [writeNodes];exact afterShort
  have positive : offset.toNat < (offset+1).toNat := by
    have fits : offset.toNat+1<2^64 := Nat.lt_of_le_of_lt bounds tree.locations.size.bytes.toNat_lt
    rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt fits];omega
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path
    (written output offset).tree writeRuntime.formed.toGraphState child node writtenAt
  obtain ⟨releaseDone,releaseShape,releaseRuntime,releaseComplete,releaseCapacity,releaseOwned⟩ :=
    S05CurrentMutableProtectorRelease.release_owned (written output offset).tree output.global extended writeRuntime writeComplete writeOrder
      position root child rootNode node slot rootAt path writtenAt hidden offset 1 positive writeActive writeOwned writtenShort
  rw [nodeTag] at releaseDone releaseShape releaseRuntime releaseComplete releaseCapacity releaseOwned
  have releaseNodes : (released output offset).tree.nodes=(written output offset).tree.nodes := by
    have framed := congrArg BorrowTree.nodes releaseShape
    exact framed
  have releaseAt : (released output offset).tree.nodeAt child=some node := by
    change (released output offset).tree.nodes.get child=_;rw [releaseNodes];exact writtenAt
  have releaseOrder := GeneralBorrowParentTagInvariant.nodes_frame (written output offset).tree (released output offset).tree releaseNodes writeOrder
  have member : (allocation,node.tag) ∈ output.frame.protectedTags.toList := by
    rw [nodeTag,tag,frameEq]
    simp [FrameState.addProtector]
  have parentOwned := S05CompletedChildReanchor.owned_end_call (released output offset).tree extended output.global output.frame allocation
    child pointer.grant node offset (offset+1) (S05ConcreteProtectedChildCompletion.child_edge completion child pointer.grant)
    releaseAt member releaseOwned
  obtain ⟨originalNode,originalAt,originalTag,_,originalExposed⟩ := metadata.old pointer.grant sourceNode present
  have originalPresent : (released output offset).tree.nodeAt pointer.grant=some originalNode := by
    change (released output offset).tree.nodes.get pointer.grant=_
    rw [releaseNodes,writeNodes];exact originalAt
  have originalProvenance : match pointer.value.provenance with
      | .concrete _ tag => tag=originalNode.tag | .wildcard => originalNode.isExposed=true := by
    cases prov : pointer.value.provenance with
    | concrete id oldTag =>
      have original : oldTag=sourceNode.tag := by simpa only [prov] using provenance
      exact original.trans originalTag.symm
    | wildcard =>
      have original : sourceNode.isExposed=true := by simpa only [prov] using provenance
      exact originalExposed.trans original
  obtain ⟨originalPosition,originalRoot,originalRootNode,originalSlot,originalRootAt,originalPath⟩ :=
    CandidateCurrentWindowAuthority.root_path (released output offset).tree releaseRuntime.formed.toGraphState pointer.grant originalNode originalPresent
  obtain ⟨depth⟩ := releaseRuntime.formed.depth
  have normal : OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal (released output offset).tree location
      (output.global.endCall output.frame).protectedTags pointer.grant)) offset (offset+1) (released output offset).tree.locations := by
    intro cursor valid isPositive start stop
    have authority := parentOwned cursor valid isPositive start stop
    apply S05CompletedAncestryNormal.normal (released output offset).tree extended _ _ releaseComplete releaseRuntime.formed.toGraphState depth
      (by change (released output offset).tree.nodes.size≤4294967296;rw [releaseNodes,writeNodes];omega)
      originalPosition originalRoot pointer.grant originalRootNode originalSlot originalRootAt originalPath
    · intro index current atNode path below
      exact (authority index current atNode).1 below
    · intro index current atNode path outside
      exact (authority index current atNode).2 outside
  exact ⟨{
    output:=output,actual:=actual,tag:=tag,globalEq:=globalEq,frameEq:=frameEq,readCompleted:=readDone,childCompleted:=childDone
    child:=child,lookup:=lookup,node:=node,childAt:=childAt,nodeTag:=nodeTag,leaf:=leaf,hidden:=hidden,metadata:=metadata,childComplete:=childComplete
    writeCompleted:=writeDone,writeRuntime:=writeRuntime,writeComplete:=writeComplete,writeOrder:=writeOrder,writeNodes:=writeNodes
    writeCapacity:=writeCapacity.trans metadata.capacity,writeActive:=writeActive,writeOwned:=writeOwned
    releaseCompleted:=releaseDone,releaseRuntime:=releaseRuntime,releaseComplete:=releaseComplete,releaseOrder:=releaseOrder,releaseShape:=releaseShape
    releaseCapacity:=releaseCapacity.trans (writeCapacity.trans metadata.capacity),releaseNode:=releaseAt,releaseOwned:=releaseOwned
    originalNode:=originalNode,originalPresent:=originalPresent,originalProvenance:=originalProvenance,originalOwned:=parentOwned,originalNormal:=normal
    afterRuntime:=fun hiddenFrame=>S05CompletedChildReanchor.runtime_end_call _ _ _ releaseRuntime hiddenFrame }⟩

end
end DuplicatePrefix.CurrentCallEmptyEntryCompleteRelease
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryCompleteRelease" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved empty complete release dependency {dependency}"
