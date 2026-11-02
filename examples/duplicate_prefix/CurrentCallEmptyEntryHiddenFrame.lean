import duplicate_prefix.CurrentCallEmptyEntryCompleteRelease
namespace DuplicatePrefix.CurrentCallEmptyEntryHiddenFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall GeneralRangeMapOrigins GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder GeneralBorrowFnEntryRegistration
open S05CompletedAncestryReadMutable (Authority)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem append_bool {tree global frame allocation completion pointer offset room}
    (borrow : CurrentCallEmptyEntryCompleteRelease.Result tree global frame allocation completion pointer offset room)
    (old : S04ReturnReleaseParent.HiddenFrame (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree frame) :
    S04ReturnReleaseParent.HiddenFrame (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree borrow.output.frame := by
  intro row member index node present tagged
  rw [borrow.frameEq] at member
  simp only [FrameState.addProtector,Array.toList_push] at member
  simp only [List.mem_append,List.mem_singleton] at member
  rcases member with previous | fresh
  · exact old row previous index node present tagged
  · subst row
    have mapped := borrow.releaseRuntime.formed.allocator.nodeTags index node present
    have childMapped := borrow.releaseRuntime.formed.allocator.nodeTags borrow.child borrow.node borrow.releaseNode
    rw [borrow.nodeTag,borrow.tag] at childMapped
    rw [tagged,childMapped] at mapped
    have same : index=borrow.child := (Option.some.inj mapped).symm
    subst index
    have nodeEq : node=borrow.node := Option.some.inj (present.symm.trans borrow.releaseNode)
    subst node;exact borrow.hidden

theorem empty {tree global frame allocation completion pointer offset room}
    (borrow : CurrentCallEmptyEntryCompleteRelease.Result tree global frame allocation completion pointer offset room)
    (shape : frame.protectedTags=#[]) :
    S04ReturnReleaseParent.HiddenFrame (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree borrow.output.frame := by
  apply append_bool borrow
  intro row member
  simp [shape] at member

theorem singleton_present {tree global frame allocation completion pointer offset room}
    (borrow : CurrentCallEmptyEntryCompleteRelease.Result tree global frame allocation completion pointer offset room)
    (id : AllocId) (tag : BorTag) (query : UniIndex) (node : TreeNode)
    (shape : frame.protectedTags=#[(id,tag)])
    (present : (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree.nodeAt query=some node)
    (nodeTag : node.tag=tag) (hidden : node.isExposed=false) :
    S04ReturnReleaseParent.HiddenFrame (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree borrow.output.frame := by
  have nodes : (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree.nodes=
      (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree.nodes := by
    have known := congrArg BorrowTree.nodes borrow.releaseShape
    exact known
  have finalAt : (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree.nodeAt query=some node := by
    change (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree.nodes.get query=_
    rw [nodes];exact present
  apply append_bool borrow
  intro row member index current found tagged
  have equal : row=(id,tag) := by simpa [shape] using member
  subst row
  have mapped := borrow.releaseRuntime.formed.allocator.nodeTags index current found
  have actual := borrow.releaseRuntime.formed.allocator.nodeTags query node finalAt
  rw [nodeTag] at actual
  rw [tagged,actual] at mapped
  have same : index=query := (Option.some.inj mapped).symm
  subst index
  have nodeEq : current=node := Option.some.inj (found.symm.trans finalAt)
  subst current;exact hidden
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

private theorem concrete_old_lookup (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (query : BorTag) (different : newTag ≠ query) :
    (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree.indexOfTag query =
      tree.indexOfTag query := by
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  exact (GeneralBorrowFreshMetadataChildMutableSlot.build tree rank runtime.formed.children runtime.formed.covered parentTag newTag
    parent parentNode tagged present fresh slot offset len nonzero runtime.formed.well runtime.formed.fits bounds).oldLookup query different

private theorem wildcard_old_lookup (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (query : BorTag) (different : tag ≠ query) :
    (tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree.indexOfTag query =
      tree.indexOfTag query := by
  obtain ⟨mapping,index,inserted,rows,_,_,_,_⟩ := GeneralBorrowWildcardConstructorSlot.select
    tree global runtime tag fresh room (.ReservedFrz false) .None
  have actual := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState tag fresh room mapping index inserted
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset len nonzero bounds
  rw [actual]
  change mapping.get query = tree.tagMapping.get query
  have equal : mapping = ⟨tree.tagMapping.mapping.push (tag,index),mapping.deassigned⟩ := by
    cases mapping
    simp_all
  rw [equal]
  exact GeneralBorrowTagMap.pushed_get_old tree.tagMapping tag query different index mapping.deassigned
private theorem singleton_absent_child {tree global frame allocation completion pointer offset room}
    (borrow : CurrentCallEmptyEntryCompleteRelease.Result tree global frame allocation completion pointer offset room)
    (id : AllocId) (tag : BorTag) (shape : frame.protectedTags=#[(id,tag)])
    (absent : borrow.output.child.tree.indexOfTag tag=none) :
    S04ReturnReleaseParent.HiddenFrame (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree borrow.output.frame := by
  have nodes : (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree.nodes=borrow.output.child.tree.nodes := by
    have known := congrArg BorrowTree.nodes borrow.releaseShape
    exact known.trans borrow.writeNodes
  apply append_bool borrow
  intro row member index current found tagged
  have equal : row=(id,tag) := by simpa [shape] using member
  subst row
  have childAt : borrow.output.child.tree.nodeAt index=some current := by
    change (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree.nodes.get index=some current at found
    change borrow.output.child.tree.nodes.get index=_
    rw [nodes] at found;exact found
  have mapped := (borrow.childComplete.2.2.2.2.1 index current childAt).1
  rw [tagged] at mapped
  change borrow.output.child.tree.indexOfTag tag=some index at mapped
  rw [mapped] at absent
  cases absent

/-- A distinct source allocation's fresh tag stays absent from this Bool tree
through the actual Read/constructor/Write/release, so the whole frame is hidden. -/
theorem singleton_other (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (pointer : PointerInstance) (sourceNode : TreeNode) (present : tree.nodes.get pointer.grant=some sourceNode)
    (provenance : match pointer.value.provenance with | .concrete _ tag => tag=sourceNode.tag | .wildcard => sourceNode.isExposed=true)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1≤4294967295) (short : tree.nodes.size+1<65536)
    (offset : UInt64) (bounds : offset.toNat+1≤tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags pointer.grant) offset (offset+1) tree.locations)
    (borrow : CurrentCallEmptyEntryCompleteRelease.Result tree global frame allocation completion pointer offset room)
    (id : AllocId) (tag : BorTag) (shape : frame.protectedTags=#[(id,tag)])
    (absent : tree.indexOfTag tag=none) (different : borrow.output.tag≠tag) :
    S04ReturnReleaseParent.HiddenFrame (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree borrow.output.frame := by
  let literal := CurrentCallTypedFnEntry.literal tree global frame allocation room pointer.value.provenance offset 1
  have outputEq : borrow.output=literal := Except.ok.inj (borrow.actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  obtain ⟨readRuntime,readComplete,readNodes,readTags,readCapacity⟩ := prepared_read tree global frame allocation completion runtime complete order
    pointer sourceNode present provenance room (by omega) offset bounds owned
  change DuplicatePrefixBorrowContract.RuntimeFacts literal.access.tree literal.global at readRuntime
  change Completes literal.access.tree completion at readComplete
  change literal.access.tree.nodes=tree.nodes at readNodes
  change literal.access.tree.tagMapping=tree.tagMapping at readTags
  change literal.access.tree.locations.size=tree.locations.size at readCapacity
  obtain ⟨_,_,_,_,_,originalFresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation room runtime
  have fresh : GeneralBorrowTagMap.Fresh literal.access.tree.tagMapping global.nextPointerTag := by rw [readTags];exact originalFresh
  have readPresent : literal.access.tree.nodeAt pointer.grant=some sourceNode := by
    change literal.access.tree.nodes.get pointer.grant=_;rw [readNodes];exact present
  have readBounds : offset.toNat+1≤literal.access.tree.locations.size.bytes.toNat := by rw [readCapacity];exact bounds
  have readRoom : literal.access.tree.nodes.size+1≤4294967295 := by rw [readNodes];exact nodeRoom
  have readAbsent : literal.access.tree.indexOfTag tag=none := by unfold BorrowTree.indexOfTag;rw [readTags];exact absent
  have tagDifferent : global.nextPointerTag≠tag := by rw [←borrow.tag];exact different
  apply singleton_absent_child borrow id tag shape
  cases prov : pointer.value.provenance with
  | concrete pointerId parentTag =>
    have parentTagEq : parentTag=sourceNode.tag := by simpa only [prov] using provenance
    have tagged : literal.access.tree.indexOfTag parentTag=some pointer.grant := by
      rw [parentTagEq];exact (readComplete.2.2.2.2.1 pointer.grant sourceNode readPresent).1
    have retained := concrete_old_lookup literal.access.tree literal.global readRuntime parentTag global.nextPointerTag pointer.grant sourceNode tagged
      readPresent fresh readRoom offset 1 (by decide) readBounds tag tagDifferent
    rw [outputEq]
    simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov,
      GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using retained.trans readAbsent
  | wildcard =>
    have retained := wildcard_old_lookup literal.access.tree literal.global readRuntime global.nextPointerTag fresh readRoom offset 1 (by decide) readBounds tag tagDifferent
    rw [outputEq]
    simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov,
      GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using retained.trans readAbsent

end
end DuplicatePrefix.CurrentCallEmptyEntryHiddenFrame
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryHiddenFrame" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved empty hidden-frame dependency {dependency}"
