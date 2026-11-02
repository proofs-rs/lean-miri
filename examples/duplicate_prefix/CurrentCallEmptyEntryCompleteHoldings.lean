import duplicate_prefix.CurrentCallEmptyEntryCompleteRelease
import duplicate_prefix.CurrentCallEmptyEntryWriteKind
import duplicate_prefix.CompletedBorrowPhysicalSource
namespace DuplicatePrefix.CurrentCallEmptyEntryCompleteHoldings
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall GeneralRangeMapOrigins GeneralRangeMapState
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowProjection OrdinaryBorrowAuthority BorrowRangeAccess
open GeneralBorrowWildcardParentTagOrder
open S05CompletedAncestryReadMutable (Authority)
open GeneralBorrowFreshActiveWithin
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

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


/-- Constructor-derived Reserved rows are an internal leaf certificate, not an
original-call admission condition. The real Write supplies both holdings. -/
theorem of_reserved (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (pointer : PointerInstance) (sourceNode : TreeNode) (present : tree.nodes.get pointer.grant=some sourceNode)
    (provenance : match pointer.value.provenance with | .concrete _ tag => tag=sourceNode.tag | .wildcard => sourceNode.isExposed=true)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1≤4294967295) (short : tree.nodes.size+1<65536)
    (offset : UInt64) (bounds : offset.toNat+1≤tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags pointer.grant) offset (offset+1) tree.locations)
    (borrow : CurrentCallEmptyEntryCompleteRelease.Result tree global frame allocation completion pointer offset room)
    (reserved : Every (fun row => (RawState row borrow.child borrow.node).permission=.ReservedFrz false) borrow.output.child.tree.locations) :
    OwnedOn (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal
      (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree row borrow.output.global.protectedTags borrow.child))
      offset (offset+1) (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree.locations ∧
    OwnedOn (Authority (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree
      (S05ConcreteProtectedChildCompletion.extend completion borrow.child pointer.grant) borrow.output.global.protectedTags borrow.child)
      offset (offset+1) (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree.locations ∧
    Every (CurrentCallEmptyEntryWriteKind.WriteOnly borrow.child)
      (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree.locations := by
  obtain ⟨output,actual,_,_,_,_,childRuntime,child,lookup,childComplete,childOwned,metadata,_⟩ :=
    CandidateCurrentFnEntryRaw.source_only tree global frame allocation completion runtime complete order pointer sourceNode present provenance
      room nodeRoom (by omega) offset 1 (by decide) bounds owned
  have outputEq : output=borrow.output := Except.ok.inj (actual.symm.trans borrow.actual)
  subst output
  have childEq : child=borrow.child := Option.some.inj (lookup.symm.trans borrow.lookup)
  subst child
  let after := borrow.output.child.tree
  let held := borrow.output.global.protectedTags
  let extended := S05ConcreteProtectedChildCompletion.extend completion borrow.child pointer.grant
  have afterBounds : offset.toNat+1≤after.locations.size.bytes.toNat := by rw [metadata.capacity];exact bounds
  have afterShort : after.nodes.size<65536 := Nat.lt_of_le_of_lt metadata.growth short
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path after childRuntime.formed.toGraphState borrow.child borrow.node borrow.childAt
  obtain ⟨depth⟩ := childRuntime.formed.depth
  obtain ⟨actualRoot,actualAt,parentless⟩ := childComplete.2.2.2.1 position root slot
  have rootEq : actualRoot=rootNode := Option.some.inj (actualAt.symm.trans rootAt)
  subst actualRoot
  have normalRows : OwnedOn (fun row => Authority after extended held borrow.child row ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Normal after row held borrow.child)) offset (offset+1) after.locations := by
    intro cursor valid positive start stop
    have authority := childOwned cursor valid positive start stop
    refine ⟨authority,?_⟩
    apply S05CompletedAncestryNormal.normal after extended _ held childComplete childRuntime.formed.toGraphState depth
      childRuntime.formed.fits position root borrow.child rootNode slot rootAt path
    · intro index current atNode walk below;exact (authority index current atNode).1 below
    · intro index current atNode walk outside;exact (authority index current atNode).2 outside
  let RP := fun row => GeneralBorrowExposureCardinality.LocationCoherent after row held ∧
    GeneralBorrowLocationSifaConsistency.Profile after row held ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible after row
  let prepared := after.locations.iterMut (Size.ofBytes offset) (Size.ofBytes 1)
  have preparedRuntime := GeneralRangeMapSafety.iter_mut RP after.locations (Size.ofBytes offset) (Size.ofBytes 1)
    childRuntime.formed.well (by intro cursor valid;exact ⟨childRuntime.coherent cursor valid,childRuntime.formed.profile cursor valid,childRuntime.possible cursor valid⟩) afterBounds
  have preparedReserved := GeneralRangeMapSafety.iter_mut (fun row => (RawState row borrow.child borrow.node).permission=.ReservedFrz false)
    after.locations (Size.ofBytes offset) (Size.ofBytes 1) childRuntime.formed.well reserved afterBounds
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on after.locations (Size.ofBytes offset) (Size.ofBytes 1)
    childRuntime.formed.well afterBounds _ offset (offset+1) normalRows (Nat.le_refl _) (Nat.le_refl _)
  have writeKinds := CurrentCallEmptyEntryWriteKind.range_write_kind after held borrow.output.tag borrow.child borrow.lookup
    (Size.ofBytes offset) (Size.ofBytes 1) .VisitChildrenOfAccessed childRuntime.formed.well afterBounds
    (by
      obtain ⟨ctorNode,ctorAt,ctorTag,ctorLeaf,ctorHidden,active⟩ := child_data tree global frame allocation completion runtime complete order
        pointer sourceNode present provenance room nodeRoom (by omega) offset bounds owned borrow.output borrow.actual borrow.tag borrow.child borrow.lookup
      exact active) (by
      intro cursor valid
      let segment := prepared.segments[cursor]'valid
      have cursorBound : cursor<prepared.positions.size := by rw [preparedRuntime.lengths];exact valid
      obtain ⟨positionBound,selectionEq⟩ := preparedRuntime.selected cursor cursorBound
      have scalarRuntime : RP segment.data := by
        rw [show segment=prepared.state.entries[prepared.positions[cursor]] from selectionEq]
        exact preparedRuntime.every _ positionBound
      have scalarReserved : (RawState segment.data borrow.child borrow.node).permission=.ReservedFrz false := by
        rw [show segment=prepared.state.entries[prepared.positions[cursor]] from selectionEq]
        exact preparedReserved.every _ positionBound
      obtain ⟨authority,⟨normal⟩⟩ := preparedOwners.2.2 cursor valid
      have row := CurrentCallEmptyEntryWriteKind.write_unique after extended segment.data held childRuntime.formed.toGraphState childComplete.2.2.1
        position root borrow.child rootNode borrow.node slot rootAt borrow.childAt path normal scalarReserved authority
        (fun index current found walk => CompletedBorrowPhysicalSource.same_root_ancestor_iff childComplete rootAt parentless found walk path)
        scalarRuntime.1 scalarRuntime.2.1 scalarRuntime.2.2 (by
          intro rootPosition other rootSlot different current currentAuthority cache profile possible currentFrame
          obtain ⟨done,removed,legal,counts,outCache,outside,outProfile,outPossible,vacant,outAuthority⟩ :=
            S05CompletedWriteAuthorityRoot.access after extended current held childComplete depth metadata.order rootPosition position other root borrow.child
              rootNode rootSlot slot rootAt different path currentAuthority childRuntime.formed.toGraphState cache afterShort profile possible
          exact ⟨done,outCache,outProfile,outPossible,outside,outAuthority⟩)
        .VisitChildrenOfAccessed segment.range
      exact ⟨row.1,row.2.2.2.2.2.2⟩)
  let written := CurrentCallEmptyEntryCompleteRelease.written borrow.output offset
  have writtenAt : written.tree.nodeAt borrow.child=some borrow.node := by
    change written.tree.nodes.get borrow.child=_;rw [borrow.writeNodes];exact borrow.childAt
  obtain ⟨wp,wr,wrNode,wslot,wrAt,wpath⟩ := CandidateCurrentWindowAuthority.root_path written.tree borrow.writeRuntime.formed.toGraphState borrow.child borrow.node writtenAt
  obtain ⟨writtenDepth⟩ := borrow.writeRuntime.formed.depth
  refine ⟨?_,borrow.writeOwned,writeKinds.2⟩
  intro cursor valid positive start stop
  have authority := borrow.writeOwned cursor valid positive start stop
  apply S05CompletedAncestryNormal.normal written.tree extended _ held borrow.writeComplete borrow.writeRuntime.formed.toGraphState writtenDepth
    borrow.writeRuntime.formed.fits wp wr borrow.child wrNode wslot wrAt wpath
  · intro index current atNode walk below;exact (authority index current atNode).1 below
  · intro index current atNode walk outside;exact (authority index current atNode).2 outside

end
end DuplicatePrefix.CurrentCallEmptyEntryCompleteHoldings

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryCompleteHoldings" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved complete holdings dependency {dependency}"
