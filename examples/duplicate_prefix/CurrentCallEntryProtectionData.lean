import duplicate_prefix.S02FnEntryOldActivity
import duplicate_prefix.S02WildcardReturnSameSourceActivity
import duplicate_prefix.S05CompletedWriteAuthorityConcrete
import duplicate_prefix.CurrentCallEntry
import duplicate_prefix.GeneralBorrowConstructorChildActivity
import duplicate_prefix.GeneralBorrowWildcardRootConstructorActivity
import duplicate_prefix.CurrentCallRootActivity

namespace DuplicatePrefix.CurrentCallEntryProtectionData
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall
open CanonicalConfigFacts ActualReferenceContext GeneralBorrowFnEntryRegistration GeneralBorrowWildcardParentTagOrder
open GeneralBorrowFreshActiveWithin GeneralRangeMapOrigins GeneralBorrowExposedNonleafPrimaryPath
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Recover the real fresh mutable node, including the fields discarded by the
older metadata API, from either actual allocator branch. -/
theorem concrete_constructor (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    ∃ child node, actual.tree.indexOfTag newTag = some child ∧ actual.tree.nodeAt child = some node ∧
      node.tag = newTag ∧ node.children = #[] ∧ node.isExposed = false ∧
      ActiveWithin actual.tree child .Write offset (offset+len) := by
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    have metadata := GeneralBorrowFreshMetadataChildMutable.append input
    obtain ⟨node,atNode,tag,_,leaf,_,hidden⟩ := metadata.newNode
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by
      have atEnd : (GeneralBorrowFreshMetadataChildMutable.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _),Option.getD_none]
    have activity := GeneralBorrowConstructorChildActivity.Protected.append input
      (fun position valid => (runtime.formed.profile position valid).vacant _ vacant)
    exact ⟨_,node,metadata.freshLookup,atNode,tag,leaf,hidden,activity⟩
  | reuse index available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,valid,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have metadata := GeneralBorrowFreshMetadataChildMutableReuse.reuse input
    obtain ⟨node,atNode,tag,_,leaf,_,hidden⟩ := metadata.newNode
    have activity := GeneralBorrowConstructorChildActivity.Protected.reuse input
      (fun position valid => (runtime.formed.profile position valid).vacant _ vacant)
    exact ⟨_,node,metadata.freshLookup,atNode,tag,leaf,hidden,activity⟩

/-- The wildcard constructor installs a hidden leaf in the same arbitrary
coherent allocator; it does not require an exposed leaf forest. -/
theorem wildcard_constructor (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    ∃ child node, actual.tree.indexOfTag tag = some child ∧ actual.tree.nodeAt child = some node ∧
      node.tag = tag ∧ node.children = #[] ∧ node.isExposed = false ∧
      ActiveWithin actual.tree child .Write offset (offset+len) := by
  obtain ⟨mapping,index,inserted,rows,vacant,graph,monotone,growth⟩ :=
    GeneralBorrowWildcardConstructorSlot.select tree global runtime tag fresh room (.ReservedFrz false) .None
  have actual := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState tag fresh room mapping index inserted
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset len nonzero bounds
  have activity := GeneralBorrowFreshActiveWithinInsert.modified tree index (Size.ofBytes offset) (Size.ofBytes len)
    GeneralBorrowFreshChild.inside .Write (by intro kind associated impossible;cases impossible)
    runtime.formed.well bounds (by intro position valid;exact (runtime.formed.profile position valid).vacant index vacant)
  have present : (GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None
      GeneralBorrowFreshChild.inside offset len).nodeAt index =
      some (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) := GeneralBorrowFreshLocation.get_same tree.nodes index _
  have lookup := graph.allocator.nodeTags index _ present
  rw [actual]
  exact ⟨index,_,lookup,present,rfl,rfl,rfl,activity⟩
private theorem prepared_bool {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) :
    let room := (CurrentCallBoolProtection.return_budget input frame raw).1
    let literal := CurrentCallTypedFnEntry.literal (CurrentCallBoolProtection.returnTree raw) raw.output.global raw.output.frame call.returnId room
      raw.returnPointer.value.provenance (UInt64.ofNat call.returnOffset) 1
    DuplicatePrefixBorrowContract.RuntimeFacts literal.access.tree literal.global ∧
      Completes literal.access.tree (CurrentCallBoolProtection.returnCompletion raw) ∧
      literal.access.tree.nodes = (CurrentCallBoolProtection.returnTree raw).nodes ∧
      literal.access.tree.tagMapping = (CurrentCallBoolProtection.returnTree raw).tagMapping ∧
      literal.access.tree.locations.size = (CurrentCallBoolProtection.returnTree raw).locations.size := by
  obtain ⟨runtime,complete,order,node,nodeAt,provenance⟩ := CurrentCallBoolProtection.return_ready input frame raw
  obtain ⟨room,_,short⟩ := CurrentCallBoolProtection.return_budget input frame raw
  have bounds := (CurrentCallBoolProtection.endpoints input frame raw positive).2.2.2.2.1
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ :=
    CandidateCurrentWindowAuthority.root_path (CurrentCallBoolProtection.returnTree raw) runtime.formed.toGraphState raw.returnPointer.grant node nodeAt
  cases prov : raw.returnPointer.value.provenance with
  | concrete id tag =>
    have tagEq : tag = node.tag := by simpa [prov] using provenance
    obtain ⟨_,afterRuntime,afterComplete,_,nodes,_,tags,capacity⟩ := S05ConcreteFnEntryRaw.prepare_read
      (CurrentCallBoolProtection.returnTree raw) raw.output.global raw.output.frame call.returnId (CurrentCallBoolProtection.returnCompletion raw) runtime complete order
      position root raw.returnPointer.grant rootNode node slot rootAt nodeAt path room (UInt64.ofNat call.returnOffset) 1
      bounds raw.boolOwned (by omega) .VisitChildrenOfAccessed
    simpa only [CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,
      prov,tagEq] using And.intro afterRuntime (And.intro afterComplete (And.intro nodes (And.intro tags capacity)))
  | wildcard =>
    have exposed : node.isExposed = true := by simpa [prov] using provenance
    obtain ⟨_,afterRuntime,afterComplete,_,nodes,_,tags,capacity⟩ := S05WildcardFnEntryRaw.prepare_read
      (CurrentCallBoolProtection.returnTree raw) raw.output.global raw.output.frame call.returnId (CurrentCallBoolProtection.returnCompletion raw) runtime complete order
      position root raw.returnPointer.grant rootNode node slot rootAt nodeAt exposed path room (UInt64.ofNat call.returnOffset) 1
      bounds raw.boolOwned (by omega) .VisitChildrenOfAccessed
    simpa only [CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,
      prov] using And.intro afterRuntime (And.intro afterComplete (And.intro nodes (And.intro tags capacity)))

theorem bool_data {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) (borrowed : CurrentCallBoolProtection.Borrowed raw) :
    ∃ node, borrowed.output.child.tree.nodes.get borrowed.child = some node ∧ node.tag = borrowed.output.tag ∧ node.children = #[] ∧ node.isExposed = false ∧
      ActiveWithin borrowed.output.child.tree borrowed.child .Write (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) := by
  obtain ⟨runtime,_,_,parentNode,parentAt,provenance⟩ := CurrentCallBoolProtection.return_ready input frame raw
  obtain ⟨room,nodeRoom,_⟩ := CurrentCallBoolProtection.return_budget input frame raw
  let literal := CurrentCallTypedFnEntry.literal (CurrentCallBoolProtection.returnTree raw) raw.output.global raw.output.frame call.returnId room
    raw.returnPointer.value.provenance (UInt64.ofNat call.returnOffset) 1
  have outputEq : borrowed.output = literal := Except.ok.inj
    (borrowed.actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  obtain ⟨readRuntime,readComplete,readNodes,readTags,readCapacity⟩ := prepared_bool input frame raw positive
  change DuplicatePrefixBorrowContract.RuntimeFacts literal.access.tree literal.global at readRuntime
  change Completes literal.access.tree (CurrentCallBoolProtection.returnCompletion raw) at readComplete
  change literal.access.tree.nodes = (CurrentCallBoolProtection.returnTree raw).nodes at readNodes
  change literal.access.tree.tagMapping = (CurrentCallBoolProtection.returnTree raw).tagMapping at readTags
  change literal.access.tree.locations.size = (CurrentCallBoolProtection.returnTree raw).locations.size at readCapacity
  obtain ⟨_,held,_,_,_,originalFresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare
    (CurrentCallBoolProtection.returnTree raw) raw.output.global raw.output.frame call.returnId room runtime
  have fresh : GeneralBorrowTagMap.Fresh literal.access.tree.tagMapping raw.output.global.nextPointerTag := by
    rw [readTags];exact originalFresh
  have currentRoom : literal.access.tree.nodes.size+1 ≤ 4294967295 := by rw [readNodes];exact nodeRoom
  have nodeAt : literal.access.tree.nodes.get raw.returnPointer.grant = some parentNode := by rw [readNodes];exact parentAt
  have bounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ literal.access.tree.locations.size.bytes.toNat := by
    rw [readCapacity];exact (CurrentCallBoolProtection.endpoints input frame raw positive).2.2.2.2.1
  have own : literal.child.tree.indexOfTag raw.output.global.nextPointerTag = some borrowed.child := by
    simpa only [outputEq,literal,CurrentCallTypedFnEntry.literal] using borrowed.childLookup
  have tagBound : raw.output.global.nextPointerTag.value.toNat < literal.global.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value raw.output.global.nextPointerTag room
    change raw.output.global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag raw.output.global.nextPointerTag room).value.toNat
    omega
  have heldTag : literal.global.protectedTags.contains raw.output.global.nextPointerTag = true := by
    change (registered raw.output.global raw.output.frame call.returnId room).1.protectedTags.contains raw.output.global.nextPointerTag = true
    unfold ProtectedTags.contains
    rw [held]
    rfl
  cases prov : raw.returnPointer.value.provenance with
  | concrete id tag =>
    have tagged : literal.access.tree.indexOfTag tag = some raw.returnPointer.grant := by
      have tagEq : tag = parentNode.tag := by simpa [prov] using provenance
      rw [tagEq]
      exact (readComplete.2.2.2.2.1 raw.returnPointer.grant parentNode nodeAt).1
    obtain ⟨child,node,lookup,found,nodeTag,leaf,hidden,activity⟩ := concrete_constructor literal.access.tree literal.global
      readRuntime tag raw.output.global.nextPointerTag raw.returnPointer.grant parentNode tagged nodeAt fresh currentRoom
      (UInt64.ofNat call.returnOffset) 1 (by decide) bounds
    have lookup' : literal.child.tree.indexOfTag raw.output.global.nextPointerTag = some child := by
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshMetadataChildMutableSlot.result,
        GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using lookup
    have same : child = borrowed.child := Option.some.inj (lookup'.symm.trans own)
    subst child
    refine ⟨node,?_,?_,leaf,hidden,?_⟩
    · rw [outputEq]
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshMetadataChildMutableSlot.result,
        GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using found
    · rw [borrowed.tag]
      exact nodeTag
    · rw [outputEq]
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using activity
  | wildcard =>
    obtain ⟨child,node,lookup,found,nodeTag,leaf,hidden,activity⟩ := wildcard_constructor
      literal.access.tree literal.global readRuntime raw.output.global.nextPointerTag fresh currentRoom
      (UInt64.ofNat call.returnOffset) 1 (by decide) bounds
    have lookup' : literal.child.tree.indexOfTag raw.output.global.nextPointerTag = some child := by
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using lookup
    have same : child = borrowed.child := Option.some.inj (lookup'.symm.trans own)
    subst child
    refine ⟨node,?_,?_,leaf,hidden,?_⟩
    · rw [outputEq]
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using found
    · rw [borrowed.tag]
      exact nodeTag
    · rw [outputEq]
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using activity


/-- The actual initial Bool Write preserves its hidden leaf and confines all
activity to the one-byte return window. -/
theorem bool_written_data {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) (borrowed : CurrentCallBoolProtection.Borrowed raw)
    (written : CurrentCallBoolProtection.Written borrowed) :
    ∃ node, (CurrentCallBoolProtection.writeResult borrowed).tree.nodes.get borrowed.child = some node ∧
      node.tag = borrowed.output.tag ∧ node.children = #[] ∧ node.isExposed = false ∧
      ActiveWithin (CurrentCallBoolProtection.writeResult borrowed).tree borrowed.child .Write
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) := by
  obtain ⟨node,present,tag,leaf,hidden,active⟩ := bool_data input frame raw positive borrowed
  have bounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ borrowed.output.child.tree.locations.size.bytes.toNat := by
    rw [borrowed.metadata.capacity]
    exact (CurrentCallBoolProtection.endpoints input frame raw positive).2.2.2.2.1
  have retained := GeneralBorrowFreshActiveWithinAccess.normal borrowed.output.child.tree borrowed.output.tag
    (Size.ofBytes (UInt64.ofNat call.returnOffset)) (Size.ofBytes 1) .Write borrowed.output.global.protectedTags
    .VisitChildrenOfAccessed borrowed.child (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1)
    borrowed.runtime.formed.well bounds (Nat.le_refl _) (Nat.le_refl _) active
  refine ⟨node,?_,tag,leaf,hidden,retained⟩
  rw [written.nodes]
  exact present

/-- The real protected-child Write retains full mutable authority on its own
window. This uses the actual completed Write rule, not its earlier Read rule. -/
theorem write_authority (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (child : UniIndex) (node : TreeNode) (present : tree.nodes.get child = some node)
    (offset : UInt64) (bounds : offset.toNat+1 ≤ tree.locations.size.bytes.toNat)
    (short : tree.nodes.size < 65536)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags child)
      offset (offset+1) tree.locations) :
    let written := tree.performBorrowAccessRange (.concrete node.tag) (Size.ofBytes offset) (Size.ofBytes 1)
      .Write global.protectedTags .VisitChildrenOfAccessed
    OwnedOn (S05CompletedAncestryReadMutable.Authority written.tree completion global.protectedTags child)
      offset (offset+1) written.tree.locations := by
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ :=
    CandidateCurrentWindowAuthority.root_path tree runtime.formed.toGraphState child node present
  obtain ⟨depth⟩ := runtime.formed.depth
  have combined : OwnedOn (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags child location)
      offset (offset+1) tree.locations := by
    intro cursor valid positive start stop
    exact ⟨runtime.possible cursor valid,owned cursor valid positive start stop⟩
  have range := S05CompletedWriteAuthorityConcrete.range tree completion global.protectedTags complete
    runtime.formed.toGraphState depth order position root child rootNode node slot rootAt present path
    (Size.ofBytes offset) (Size.ofBytes 1) offset (offset+1) combined runtime.formed.well
    (fun cursor valid => ⟨runtime.coherent cursor valid,runtime.formed.profile cursor valid,runtime.possible cursor valid⟩)
    bounds (Nat.le_refl _) (Nat.le_refl _) short .VisitChildrenOfAccessed
  dsimp only
  intro cursor valid positive start stop index current found
  exact (range.rows cursor valid positive start stop).2 index current (by rw [←range.nodes];exact found)

/-- Full Bool-child authority after the actual initial writeUninit access;
the physical byte initialization-mask update does not alter this tree. -/
theorem bool_written_authority {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) (borrowed : CurrentCallBoolProtection.Borrowed raw) :
    OwnedOn (S05CompletedAncestryReadMutable.Authority (CurrentCallBoolProtection.writeResult borrowed).tree
      (S05ConcreteProtectedChildCompletion.extend (CurrentCallBoolProtection.returnCompletion raw) borrowed.child raw.returnPointer.grant)
      borrowed.output.global.protectedTags borrowed.child)
      (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1)
      (CurrentCallBoolProtection.writeResult borrowed).tree.locations := by
  obtain ⟨node,present,tag,_,_,_⟩ := bool_data input frame raw positive borrowed
  have bounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ borrowed.output.child.tree.locations.size.bytes.toNat := by
    rw [borrowed.metadata.capacity]
    exact (CurrentCallBoolProtection.endpoints input frame raw positive).2.2.2.2.1
  have short : borrowed.output.child.tree.nodes.size < 65536 := by
    have budget := (CurrentCallBoolProtection.return_budget input frame raw).2.2
    have growth := borrowed.metadata.growth
    omega
  have retained := write_authority borrowed.output.child.tree borrowed.output.global
    (S05ConcreteProtectedChildCompletion.extend (CurrentCallBoolProtection.returnCompletion raw) borrowed.child raw.returnPointer.grant)
    borrowed.runtime borrowed.completes borrowed.metadata.order borrowed.child node present
    (UInt64.ofNat call.returnOffset) bounds short borrowed.boolOwned
  simpa only [tag,CurrentCallBoolProtection.writeResult] using retained

private theorem source_ready {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) :
    DuplicatePrefixBorrowContract.RuntimeFacts raw.sourceAllocation.extra tracker.global ∧
      Completes raw.sourceAllocation.extra raw.sourcePrecise.completion ∧
      ParentTagOrder raw.sourceAllocation.extra ∧ raw.sourceAllocation.extra.nodes.size+1 ≤ 4294967295 ∧
      raw.sourceAllocation.extra.nodes.size < 65536 ∧
      (UInt64.ofNat call.sourceOffset).toNat+len.toNat ≤ raw.sourceAllocation.extra.locations.size.bytes.toNat ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority raw.sourceAllocation.extra raw.sourcePrecise.completion
        tracker.global.protectedTags raw.sourcePointer.grant)
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) raw.sourceAllocation.extra.locations ∧
      ∃ node, raw.sourceAllocation.extra.nodeAt raw.sourcePointer.grant = some node ∧
        (match raw.sourcePointer.value.provenance with
          | .concrete _ tag => tag = node.tag | .wildcard => node.isExposed = true) := by
  have live := CandidateCurrentLiveRuntime.live options limits remaining before tracker len input.machine.state input.machine.resources
  obtain ⟨runtime,order,room,short,lengthRoom,capacity⟩ := live _ _ raw.sourcePresent
  obtain ⟨allocation,present,complete,_,_⟩ := input.machine.completed call.sourceId raw.sourcePrecise raw.sourcePreciseAt
  have same := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList input.machine.worldIds
    call.sourceId allocation raw.sourceAllocation present raw.sourcePresent
  subst allocation
  obtain ⟨sp,rp,_,_,_,_,sourceUniform,_⟩ := CandidateCurrentUniformOwnerWindow.positive_call_uniform
    before tracker.global.protectedTags data call argument len place input.joint input.actualBindings input.normalizedWindows input.claims positive
  obtain ⟨loan,allocation,precise,loanAt,pointerAt,_,allocationAt,preciseAt,rights⟩ := sourceUniform
  have loanEq := Option.some.inj (loanAt.symm.trans raw.sourceLoanAt)
  subst loan
  have pointerEq := Option.some.inj (pointerAt.symm.trans raw.sourcePointerAt)
  subst sp
  have allocationEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList input.machine.worldIds
    call.sourceId allocation raw.sourceAllocation allocationAt raw.sourcePresent
  subst allocation
  have preciseEq := CandidateCurrentUniformOwnerWindow.same_id data.interpretation.precise.toList input.machine.completionIds
    call.sourceId precise raw.sourcePrecise preciseAt raw.sourcePreciseAt
  subst precise
  obtain ⟨windowBounds,_,lengthNat,_,owned⟩ := CandidateCurrentWindowAuthority.nat_window raw.sourceAllocation tracker.global.protectedTags
    raw.sourcePrecise raw.sourcePointer call.sourceId call.sourceOffset call.length .mut
    (by rw [input.actual.length];exact positive) (by decide) runtime.formed.well lengthRoom rights
  have lengthEq : UInt64.ofNat call.length = len := by
    apply UInt64.toNat_inj.mp
    rw [lengthNat,input.actual.length]
  rw [lengthEq] at owned
  have endpoints := CurrentCallBoolProtection.endpoints input frame raw positive
  have bounds : (UInt64.ofNat call.sourceOffset).toNat+len.toNat ≤ raw.sourceAllocation.extra.locations.size.bytes.toNat := by
    rw [capacity,endpoints.1]
    rw [input.actual.length] at windowBounds
    exact windowBounds
  obtain ⟨other,otherAt,binds⟩ := input.actual.instances raw.sourcePointer
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? raw.sourcePointerAt))
  rw [raw.sourceId] at otherAt
  have otherEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList input.machine.worldIds
    call.sourceId other raw.sourceAllocation otherAt raw.sourcePresent
  subst other
  obtain ⟨sourceNode,sourceAt,_,provenance⟩ := binds
  refine ⟨runtime,complete,order,room,short,bounds,owned,sourceNode,sourceAt,?_⟩
  cases prov : raw.sourcePointer.value.provenance with
  | concrete id tag =>
    simp only [prov] at provenance
    exact provenance.2
  | wildcard => simpa only [prov] using provenance
private theorem prepared_source {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) :
    let room := raw.tagRoom
    let literal := CurrentCallTypedFnEntry.literal raw.sourceAllocation.extra tracker.global frame call.sourceId room
      raw.sourcePointer.value.provenance (UInt64.ofNat call.sourceOffset) len
    DuplicatePrefixBorrowContract.RuntimeFacts literal.access.tree literal.global ∧
      Completes literal.access.tree raw.sourcePrecise.completion ∧
      literal.access.tree.nodes = raw.sourceAllocation.extra.nodes ∧
      literal.access.tree.tagMapping = raw.sourceAllocation.extra.tagMapping ∧
      literal.access.tree.locations.size = raw.sourceAllocation.extra.locations.size := by
  obtain ⟨runtime,complete,order,nodeRoom,short,bounds,owned,node,nodeAt,provenance⟩ := source_ready input frame raw positive
  let room := raw.tagRoom
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ :=
    CandidateCurrentWindowAuthority.root_path raw.sourceAllocation.extra runtime.formed.toGraphState raw.sourcePointer.grant node nodeAt
  cases prov : raw.sourcePointer.value.provenance with
  | concrete id tag =>
    have tagEq : tag = node.tag := by simpa [prov] using provenance
    obtain ⟨_,afterRuntime,afterComplete,_,nodes,_,tags,capacity⟩ := S05ConcreteFnEntryRaw.prepare_read
      raw.sourceAllocation.extra tracker.global frame call.sourceId raw.sourcePrecise.completion runtime complete order
      position root raw.sourcePointer.grant rootNode node slot rootAt nodeAt path room (UInt64.ofNat call.sourceOffset) len
      bounds owned (by omega) .VisitChildrenOfAccessed
    simpa only [CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,
      prov,tagEq] using And.intro afterRuntime (And.intro afterComplete (And.intro nodes (And.intro tags capacity)))
  | wildcard =>
    have exposed : node.isExposed = true := by simpa [prov] using provenance
    obtain ⟨_,afterRuntime,afterComplete,_,nodes,_,tags,capacity⟩ := S05WildcardFnEntryRaw.prepare_read
      raw.sourceAllocation.extra tracker.global frame call.sourceId raw.sourcePrecise.completion runtime complete order
      position root raw.sourcePointer.grant rootNode node slot rootAt nodeAt exposed path room (UInt64.ofNat call.sourceOffset) len
      bounds owned (by omega) .VisitChildrenOfAccessed
    simpa only [CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,
      prov] using And.intro afterRuntime (And.intro afterComplete (And.intro nodes (And.intro tags capacity)))

theorem source_data {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) :
    ∃ node, raw.output.child.tree.nodes.get raw.child = some node ∧ node.tag = raw.output.tag ∧ node.children = #[] ∧ node.isExposed = false ∧
      ActiveWithin raw.output.child.tree raw.child .Write (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) := by
  obtain ⟨runtime,_,_,nodeRoom,_,boundsOriginal,_,parentNode,parentAt,provenance⟩ := source_ready input frame raw positive
  let room := raw.tagRoom
  let literal := CurrentCallTypedFnEntry.literal raw.sourceAllocation.extra tracker.global frame call.sourceId room
    raw.sourcePointer.value.provenance (UInt64.ofNat call.sourceOffset) len
  have outputEq : raw.output = literal := Except.ok.inj
    (raw.actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  obtain ⟨readRuntime,readComplete,readNodes,readTags,readCapacity⟩ := prepared_source input frame raw positive
  change DuplicatePrefixBorrowContract.RuntimeFacts literal.access.tree literal.global at readRuntime
  change Completes literal.access.tree raw.sourcePrecise.completion at readComplete
  change literal.access.tree.nodes = raw.sourceAllocation.extra.nodes at readNodes
  change literal.access.tree.tagMapping = raw.sourceAllocation.extra.tagMapping at readTags
  change literal.access.tree.locations.size = raw.sourceAllocation.extra.locations.size at readCapacity
  obtain ⟨_,held,_,_,_,originalFresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare
    raw.sourceAllocation.extra tracker.global frame call.sourceId room runtime
  have fresh : GeneralBorrowTagMap.Fresh literal.access.tree.tagMapping tracker.global.nextPointerTag := by
    rw [readTags];exact originalFresh
  have currentRoom : literal.access.tree.nodes.size+1 ≤ 4294967295 := by rw [readNodes];exact nodeRoom
  have nodeAt : literal.access.tree.nodes.get raw.sourcePointer.grant = some parentNode := by rw [readNodes];exact parentAt
  have bounds : (UInt64.ofNat call.sourceOffset).toNat+len.toNat ≤ literal.access.tree.locations.size.bytes.toNat := by
    rw [readCapacity];exact boundsOriginal
  have own : literal.child.tree.indexOfTag tracker.global.nextPointerTag = some raw.child := by
    simpa only [outputEq,literal,CurrentCallTypedFnEntry.literal] using raw.childLookup
  have tagBound : tracker.global.nextPointerTag.value.toNat < literal.global.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have heldTag : literal.global.protectedTags.contains tracker.global.nextPointerTag = true := by
    change (registered tracker.global frame call.sourceId room).1.protectedTags.contains tracker.global.nextPointerTag = true
    unfold ProtectedTags.contains
    rw [held]
    rfl
  cases prov : raw.sourcePointer.value.provenance with
  | concrete id tag =>
    have tagged : literal.access.tree.indexOfTag tag = some raw.sourcePointer.grant := by
      have tagEq : tag = parentNode.tag := by simpa [prov] using provenance
      rw [tagEq]
      exact (readComplete.2.2.2.2.1 raw.sourcePointer.grant parentNode nodeAt).1
    obtain ⟨child,node,lookup,found,nodeTag,leaf,hidden,activity⟩ := concrete_constructor literal.access.tree literal.global
      readRuntime tag tracker.global.nextPointerTag raw.sourcePointer.grant parentNode tagged nodeAt fresh currentRoom
      (UInt64.ofNat call.sourceOffset) len (by intro h;subst len;simp at positive) bounds
    have lookup' : literal.child.tree.indexOfTag tracker.global.nextPointerTag = some child := by
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshMetadataChildMutableSlot.result,
        GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using lookup
    have same : child = raw.child := Option.some.inj (lookup'.symm.trans own)
    subst child
    refine ⟨node,?_,?_,leaf,hidden,?_⟩
    · rw [outputEq]
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshMetadataChildMutableSlot.result,
        GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using found
    · rw [raw.tag]
      exact nodeTag
    · rw [outputEq]
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using activity
  | wildcard =>
    obtain ⟨child,node,lookup,found,nodeTag,leaf,hidden,activity⟩ := wildcard_constructor
      literal.access.tree literal.global readRuntime tracker.global.nextPointerTag fresh currentRoom
      (UInt64.ofNat call.sourceOffset) len (by intro h;subst len;simp at positive) bounds
    have lookup' : literal.child.tree.indexOfTag tracker.global.nextPointerTag = some child := by
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using lookup
    have same : child = raw.child := Option.some.inj (lookup'.symm.trans own)
    subst child
    refine ⟨node,?_,?_,leaf,hidden,?_⟩
    · rw [outputEq]
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using found
    · rw [raw.tag]
      exact nodeTag
    · rw [outputEq]
      simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,
        CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using activity



/-- An actual protected concrete constructor preserves every nonparent old
node's tag, children and exposure, including reused allocator slots. -/
theorem concrete_old_node (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (query : UniIndex) (node : TreeNode) (found : tree.nodeAt query = some node) (notParent : query ≠ parent) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    ∃ next, actual.tree.nodeAt query = some next ∧ next.tag = node.tag ∧
      next.children = node.children ∧ next.isExposed = node.isExposed := by
  dsimp only
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    let index := GeneralBorrowFreshMetadataChildMutable.index input
    have notNew : query ≠ index := by
      intro equal
      have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes query node found
      have atEnd : index.toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
      rw [equal,atEnd] at bounded
      omega
    have attached := GeneralBorrowFreshGraph.other_lookup tree index parent query parentNode
      (GeneralBorrowFreshChild.child newTag parent) (GeneralBorrowFreshMetadataChildMutable.at_end input) present notParent notNew
    have staged : (GeneralBorrowFreshMetadataChildMutable.stage input).nodeAt query = some node := by
      simpa only [GeneralBorrowFreshMetadataChildMutable.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,
        BorrowTree.nodeAt] using attached.trans found
    obtain ⟨next,lookup,tag,_,children,_⟩ := GeneralBorrowFreshMetadata.node_fields _ _
      (GeneralBorrowFreshMetadataChildMutable.shape input) query node staged
    have exposure := GeneralBorrowFreshMetadataChildSifa.lookup_exposure _ _ (GeneralBorrowFreshMetadataChildMutable.exposure input) query
    change (GeneralBorrowFreshMetadataChildMutable.stage input).nodes.get query = some node at staged
    rw [lookup,staged] at exposure
    exact ⟨next,lookup,tag,children,by simpa only [Option.map_some,Option.some.injEq] using exposure⟩
  | reuse index available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,valid,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have notNew : query ≠ index := by
      intro equal
      change tree.nodes.get query = some node at found
      rw [equal,vacant] at found
      cases found
    have attached := GeneralBorrowFreshMetadataChildReuseGraph.other_lookup tree index parent query parentNode
      (GeneralBorrowFreshChild.child newTag parent) vacant present notParent notNew
    have staged : (GeneralBorrowFreshMetadataChildMutableReuse.stage input).nodeAt query = some node := by
      simpa only [GeneralBorrowFreshMetadataChildMutableReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,
        BorrowTree.nodeAt,GeneralBorrowFreshMetadataChildMutableReuse.index,input] using attached.trans found
    obtain ⟨next,lookup,tag,_,children,_⟩ := GeneralBorrowFreshMetadata.node_fields _ _
      (GeneralBorrowFreshMetadataChildMutableReuse.shape input) query node staged
    have exposure := GeneralBorrowFreshMetadataChildSifa.lookup_exposure _ _ (GeneralBorrowFreshMetadataChildMutableReuse.exposure input) query
    change (GeneralBorrowFreshMetadataChildMutableReuse.stage input).nodes.get query = some node at staged
    rw [lookup,staged] at exposure
    exact ⟨next,lookup,tag,children,by simpa only [Option.map_some,Option.some.injEq] using exposure⟩

/-- The Bool protector attaches to its original grant, which predates the
fresh source child even when both windows share one allocation. -/
theorem source_ne_return_parent {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) (same : call.sourceId = call.returnId) :
    raw.child ≠ raw.returnPointer.grant := by
  obtain ⟨runtime,_,_,_,_,_,_,_⟩ := source_ready input frame raw positive
  obtain ⟨other,otherAt,binds⟩ := input.actual.instances raw.returnPointer
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? raw.returnPointerAt))
  rw [raw.returnId,←same] at otherAt
  have otherEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList input.machine.worldIds
    call.sourceId other raw.sourceAllocation otherAt raw.sourcePresent
  subst other
  obtain ⟨node,nodeAt,_,_⟩ := binds
  have older := GeneralBorrowParentTagInvariant.parent_below_fresh raw.sourceAllocation.extra tracker.global runtime
    raw.returnPointer.grant node nodeAt
  obtain ⟨next,nextAt,tag,_,_⟩ := raw.oldNodes raw.returnPointer.grant node nodeAt
  obtain ⟨fresh,freshAt,freshTag⟩ := raw.childNode
  intro equal
  rw [equal,nextAt] at freshAt
  have nodeEq : next = fresh := Option.some.inj freshAt
  have tagEq : node.tag = tracker.global.nextPointerTag := tag.symm.trans ((congrArg TreeNode.tag nodeEq).trans (freshTag.trans raw.tag))
  rw [tagEq] at older
  exact Nat.lt_irrefl _ older
theorem source_same_bool_data {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) (borrowed : CurrentCallBoolProtection.Borrowed raw) (same : call.sourceId = call.returnId) :
    ∃ node, borrowed.output.child.tree.nodes.get raw.child = some node ∧
      node.tag = raw.output.tag ∧ node.children = #[] ∧ node.isExposed = false ∧
      ActiveWithin borrowed.output.child.tree raw.child .Write
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) := by
  obtain ⟨runtime,complete,order,parentNode,parentAt,provenance⟩ := CurrentCallBoolProtection.return_ready input frame raw
  obtain ⟨room,nodeRoom,_⟩ := CurrentCallBoolProtection.return_budget input frame raw
  let literal := CurrentCallTypedFnEntry.literal (CurrentCallBoolProtection.returnTree raw) raw.output.global raw.output.frame call.returnId room
    raw.returnPointer.value.provenance (UInt64.ofNat call.returnOffset) 1
  have outputEq : borrowed.output = literal := Except.ok.inj
    (borrowed.actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  obtain ⟨readRuntime,readComplete,readNodes,readTags,readCapacity⟩ := prepared_bool input frame raw positive
  change DuplicatePrefixBorrowContract.RuntimeFacts literal.access.tree literal.global at readRuntime
  change Completes literal.access.tree (CurrentCallBoolProtection.returnCompletion raw) at readComplete
  change literal.access.tree.nodes = (CurrentCallBoolProtection.returnTree raw).nodes at readNodes
  change literal.access.tree.tagMapping = (CurrentCallBoolProtection.returnTree raw).tagMapping at readTags
  change literal.access.tree.locations.size = (CurrentCallBoolProtection.returnTree raw).locations.size at readCapacity
  obtain ⟨_,held,_,_,_,originalFresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare
    (CurrentCallBoolProtection.returnTree raw) raw.output.global raw.output.frame call.returnId room runtime
  have fresh : GeneralBorrowTagMap.Fresh literal.access.tree.tagMapping raw.output.global.nextPointerTag := by
    rw [readTags];exact originalFresh
  have currentRoom : literal.access.tree.nodes.size+1 ≤ 4294967295 := by rw [readNodes];exact nodeRoom
  have nodeAt : literal.access.tree.nodes.get raw.returnPointer.grant = some parentNode := by rw [readNodes];exact parentAt
  have bounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ literal.access.tree.locations.size.bytes.toNat := by
    rw [readCapacity];exact (CurrentCallBoolProtection.endpoints input frame raw positive).2.2.2.2.1
  have own : literal.child.tree.indexOfTag raw.output.global.nextPointerTag = some borrowed.child := by
    simpa only [outputEq,literal,CurrentCallTypedFnEntry.literal] using borrowed.childLookup
  have tagBound : raw.output.global.nextPointerTag.value.toNat < literal.global.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value raw.output.global.nextPointerTag room
    change raw.output.global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag raw.output.global.nextPointerTag room).value.toNat
    omega
  have heldTag : literal.global.protectedTags.contains raw.output.global.nextPointerTag = true := by
    change (registered raw.output.global raw.output.frame call.returnId room).1.protectedTags.contains raw.output.global.nextPointerTag = true
    unfold ProtectedTags.contains
    rw [held]
    rfl

  obtain ⟨queryNode,queryAt,queryTag,queryLeaf,queryHidden,queryActive⟩ := source_data input frame raw positive
  have initialQuery : (CurrentCallBoolProtection.returnTree raw).nodeAt raw.child = some queryNode := by
    simpa only [CurrentCallBoolProtection.returnTree,if_pos same,BorrowTree.nodeAt] using queryAt
  have initialActive : ActiveWithin (CurrentCallBoolProtection.returnTree raw) raw.child .Write
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) := by
    simpa only [CurrentCallBoolProtection.returnTree,if_pos same] using queryActive
  have readQuery : literal.access.tree.nodeAt raw.child = some queryNode := by
    change literal.access.tree.nodes.get raw.child = some queryNode
    rw [readNodes]
    exact initialQuery
  have different := source_ne_return_parent input frame raw positive same
  obtain ⟨_,_,_,registeredRuntime,nodeFresh,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare
    (CurrentCallBoolProtection.returnTree raw) raw.output.global raw.output.frame call.returnId room runtime
  have registeredOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority (CurrentCallBoolProtection.returnTree raw)
      (CurrentCallBoolProtection.returnCompletion raw) literal.global.protectedTags raw.returnPointer.grant)
      (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) (CurrentCallBoolProtection.returnTree raw).locations := by
    intro cursor valid positive start stop index node present
    have flags := ProtectorInsertion.contains_other raw.output.global.protectedTags raw.output.global.nextPointerTag node.tag .StrongProtector
      (nodeFresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get _ index node).mpr present)))
    change literal.global.protectedTags.contains node.tag = _ at flags
    change (_ → _) ∧ (_ → _)
    rw [flags]
    exact raw.boolOwned cursor valid positive start stop index node present
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path
    (CurrentCallBoolProtection.returnTree raw) runtime.formed.toGraphState raw.returnPointer.grant parentNode parentAt
  have boundsInitial := (CurrentCallBoolProtection.endpoints input frame raw positive).2.2.2.2.1
  cases prov : raw.returnPointer.value.provenance with
  | concrete id tag =>
    have tagEq : tag = parentNode.tag := by simpa [prov] using provenance
    have initialTagged : (CurrentCallBoolProtection.returnTree raw).indexOfTag tag = some raw.returnPointer.grant := by
      rw [tagEq]
      exact (complete.2.2.2.2.1 raw.returnPointer.grant parentNode parentAt).1
    have readActive := CurrentCallRootActivity.concrete (CurrentCallBoolProtection.returnTree raw) literal.global registeredRuntime
      (CurrentCallBoolProtection.returnCompletion raw) complete position root raw.returnPointer.grant raw.child rootNode parentNode
      slot rootAt parentAt path tag initialTagged (UInt64.ofNat call.returnOffset) 1 boundsInitial registeredOwned
      queryNode initialQuery queryLeaf queryHidden different (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len)
      initialActive .Read .VisitChildrenOfAccessed
    have tagged : literal.access.tree.indexOfTag tag = some raw.returnPointer.grant := by
      rw [tagEq]
      exact (readComplete.2.2.2.2.1 raw.returnPointer.grant parentNode nodeAt).1
    have active := S02FnEntryOldActivity.constructor literal.access.tree literal.global readRuntime
      tag raw.output.global.nextPointerTag raw.returnPointer.grant parentNode tagged nodeAt fresh currentRoom
      (UInt64.ofNat call.returnOffset) 1 (by decide) bounds raw.child queryNode readQuery
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) (by
        simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov] using readActive)
    obtain ⟨next,nextAt,nextTag,nextChildren,nextHidden⟩ := concrete_old_node literal.access.tree literal.global readRuntime
      tag raw.output.global.nextPointerTag raw.returnPointer.grant parentNode tagged nodeAt fresh currentRoom
      (UInt64.ofNat call.returnOffset) 1 (by decide) bounds raw.child queryNode readQuery different
    rw [outputEq]
    refine ⟨next,?_,nextTag.trans queryTag,nextChildren.trans queryLeaf,nextHidden.trans queryHidden,?_⟩
    · simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using nextAt
    · simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov,
        GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using active
  | wildcard =>
    have readActive := S02HiddenLeafQuietWildcardRange.wildcard (CurrentCallBoolProtection.returnTree raw) literal.global
      registeredRuntime (UInt64.ofNat call.returnOffset) 1 boundsInitial raw.child queryNode initialQuery queryLeaf queryHidden
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) initialActive .Read .VisitChildrenOfAccessed
    obtain ⟨active,nextAt⟩ := S02WildcardReturnSameSourceActivity.constructor literal.access.tree literal.global readRuntime
      raw.output.global.nextPointerTag fresh currentRoom (UInt64.ofNat call.returnOffset) 1 (by decide) bounds raw.child queryNode readQuery
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) (by
        simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov] using readActive)
    rw [outputEq]
    refine ⟨queryNode,?_,queryTag,queryLeaf,queryHidden,?_⟩
    · simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,BorrowTree.nodeAt] using nextAt
    · simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov,
        GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using active

/-- The freshly registered Bool tag strictly follows the source child tag. -/
theorem source_bool_tags_ne {before tracker frame argument len place call data}
    (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (borrowed : CurrentCallBoolProtection.Borrowed raw) : raw.output.tag ≠ borrowed.output.tag := by
  have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag raw.tagRoom
  have next : raw.output.global.nextPointerTag = TypedRetagEmpty.successorTag tracker.global.nextPointerTag raw.tagRoom :=
    congrArg GlobalState.nextPointerTag raw.outputGlobal
  have older : raw.output.tag.value.toNat < raw.output.global.nextPointerTag.value.toNat := by
    rw [raw.tag,next]
    omega
  intro equal
  rw [equal,borrowed.tag] at older
  exact Nat.lt_irrefl _ older

/-- The actual Bool child's concrete Write preserves the distinct source leaf
and its bytewise activity. Both are facts of the current shared tree. -/
theorem source_same_written_data {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) (borrowed : CurrentCallBoolProtection.Borrowed raw)
    (written : CurrentCallBoolProtection.Written borrowed) (same : call.sourceId = call.returnId) :
    ∃ node, (CurrentCallBoolProtection.writeResult borrowed).tree.nodes.get raw.child = some node ∧
      node.tag = raw.output.tag ∧ node.children = #[] ∧ node.isExposed = false ∧
      ActiveWithin (CurrentCallBoolProtection.writeResult borrowed).tree raw.child .Write
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) := by
  obtain ⟨node,present,tag,leaf,hidden,active⟩ := source_same_bool_data input frame raw positive borrowed same
  obtain ⟨boolNode,boolPresent,boolTag,_,_,_⟩ := bool_data input frame raw positive borrowed
  have different : raw.child ≠ borrowed.child := by
    intro equal
    have nodeEq : node = boolNode := Option.some.inj (present.symm.trans (by rw [equal];exact boolPresent))
    exact source_bool_tags_ne raw borrowed (tag.symm.trans ((congrArg TreeNode.tag nodeEq).trans boolTag))
  have bounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ borrowed.output.child.tree.locations.size.bytes.toNat := by
    rw [borrowed.metadata.capacity]
    exact (CurrentCallBoolProtection.endpoints input frame raw positive).2.2.2.2.1
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path
    borrowed.output.child.tree borrowed.runtime.formed.toGraphState borrowed.child boolNode boolPresent
  have retained := CurrentCallRootActivity.concrete borrowed.output.child.tree borrowed.output.global borrowed.runtime
    (S05ConcreteProtectedChildCompletion.extend (CurrentCallBoolProtection.returnCompletion raw) borrowed.child raw.returnPointer.grant)
    borrowed.completes position root borrowed.child raw.child rootNode boolNode slot rootAt boolPresent path borrowed.output.tag
    borrowed.childLookup (UInt64.ofNat call.returnOffset) 1 bounds borrowed.boolOwned node present leaf hidden different
    (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) active .Write .VisitChildrenOfAccessed
  refine ⟨node,?_,tag,leaf,hidden,retained⟩
  rw [written.nodes]
  exact present

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
theorem source_tag_absent_bool {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (positive : 0 < len.toNat) (borrowed : CurrentCallBoolProtection.Borrowed raw) (separate : call.sourceId ≠ call.returnId) :
    borrowed.output.child.tree.indexOfTag raw.output.tag = none := by
  obtain ⟨runtime,_,_,parentNode,parentAt,provenance⟩ := CurrentCallBoolProtection.return_ready input frame raw
  obtain ⟨room,nodeRoom,_⟩ := CurrentCallBoolProtection.return_budget input frame raw
  let literal := CurrentCallTypedFnEntry.literal (CurrentCallBoolProtection.returnTree raw) raw.output.global raw.output.frame call.returnId room
    raw.returnPointer.value.provenance (UInt64.ofNat call.returnOffset) 1
  have outputEq : borrowed.output = literal := Except.ok.inj
    (borrowed.actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  obtain ⟨readRuntime,readComplete,readNodes,readTags,readCapacity⟩ := prepared_bool input frame raw positive
  change DuplicatePrefixBorrowContract.RuntimeFacts literal.access.tree literal.global at readRuntime
  change Completes literal.access.tree (CurrentCallBoolProtection.returnCompletion raw) at readComplete
  change literal.access.tree.nodes = (CurrentCallBoolProtection.returnTree raw).nodes at readNodes
  change literal.access.tree.tagMapping = (CurrentCallBoolProtection.returnTree raw).tagMapping at readTags
  change literal.access.tree.locations.size = (CurrentCallBoolProtection.returnTree raw).locations.size at readCapacity
  obtain ⟨_,held,_,_,_,originalFresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare
    (CurrentCallBoolProtection.returnTree raw) raw.output.global raw.output.frame call.returnId room runtime
  have fresh : GeneralBorrowTagMap.Fresh literal.access.tree.tagMapping raw.output.global.nextPointerTag := by
    rw [readTags];exact originalFresh
  have currentRoom : literal.access.tree.nodes.size+1 ≤ 4294967295 := by rw [readNodes];exact nodeRoom
  have nodeAt : literal.access.tree.nodes.get raw.returnPointer.grant = some parentNode := by rw [readNodes];exact parentAt
  have bounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ literal.access.tree.locations.size.bytes.toNat := by
    rw [readCapacity];exact (CurrentCallBoolProtection.endpoints input frame raw positive).2.2.2.2.1
  have own : literal.child.tree.indexOfTag raw.output.global.nextPointerTag = some borrowed.child := by
    simpa only [outputEq,literal,CurrentCallTypedFnEntry.literal] using borrowed.childLookup
  have tagBound : raw.output.global.nextPointerTag.value.toNat < literal.global.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value raw.output.global.nextPointerTag room
    change raw.output.global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag raw.output.global.nextPointerTag room).value.toNat
    omega
  have heldTag : literal.global.protectedTags.contains raw.output.global.nextPointerTag = true := by
    change (registered raw.output.global raw.output.frame call.returnId room).1.protectedTags.contains raw.output.global.nextPointerTag = true
    unfold ProtectedTags.contains
    rw [held]
    rfl

  have live := CandidateCurrentLiveRuntime.live options limits remaining before tracker len input.machine.state input.machine.resources
  have originalRuntime := (live call.returnId raw.returnAllocation raw.returnPresent).1
  obtain ⟨_,_,_,_,_,originalTagFresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare raw.returnAllocation.extra
    tracker.global frame call.sourceId raw.tagRoom originalRuntime
  have originalAbsent : (CurrentCallBoolProtection.returnTree raw).indexOfTag raw.output.tag = none := by
    simp only [CurrentCallBoolProtection.returnTree,if_neg separate,raw.tag,BorrowTree.indexOfTag,UniKeyMap.get,
      GeneralBorrowTagMap.fresh_find _ _ originalTagFresh,Option.map_none]
  have readAbsent : literal.access.tree.indexOfTag raw.output.tag = none := by
    unfold BorrowTree.indexOfTag
    rw [readTags]
    exact originalAbsent
  have different : raw.output.global.nextPointerTag ≠ raw.output.tag := by
    rw [←borrowed.tag]
    exact Ne.symm (source_bool_tags_ne raw borrowed)
  cases prov : raw.returnPointer.value.provenance with
  | concrete id tag =>
    have tagged : literal.access.tree.indexOfTag tag = some raw.returnPointer.grant := by
      have tagEq : tag = parentNode.tag := by simpa [prov] using provenance
      rw [tagEq]
      exact (readComplete.2.2.2.2.1 raw.returnPointer.grant parentNode nodeAt).1
    have preserved := concrete_old_lookup literal.access.tree literal.global readRuntime tag raw.output.global.nextPointerTag
      raw.returnPointer.grant parentNode tagged nodeAt fresh currentRoom (UInt64.ofNat call.returnOffset) 1 (by decide)
      bounds raw.output.tag different
    rw [outputEq]
    simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov,
      GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using preserved.trans readAbsent
  | wildcard =>
    have preserved := wildcard_old_lookup literal.access.tree literal.global readRuntime raw.output.global.nextPointerTag
      fresh currentRoom (UInt64.ofNat call.returnOffset) 1 (by decide) bounds raw.output.tag different
    rw [outputEq]
    simpa only [literal,CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov,
      GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using preserved.trans readAbsent

namespace Facts
variable {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {frames : Array CompilerFrameContext.ActualFrame} {out : CurrentCallEntry.Output input frames} {count : UInt64}

/-- The source protector's actual freshly installed node before the Bool retag. -/
theorem source_initial_data (_facts : CurrentCallEntry.Facts out count) (positive : 0 < len.toNat) :
    ∃ node, out.source.base.raw.output.child.tree.nodes.get out.source.base.raw.child = some node ∧
      node.tag = out.source.base.raw.output.tag ∧ node.children = #[] ∧ node.isExposed = false ∧
      ActiveWithin out.source.base.raw.output.child.tree out.source.base.raw.child .Write
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) :=
  source_data (CurrentCallPush.prepared_input input frames) {} out.source.base.raw positive

/-- Entry Facts retain the concrete Bool leaf after the actual uninitializing
Write. This is output data, not an additional admission condition. -/
theorem bool_data (facts : CurrentCallEntry.Facts out count) (positive : 0 < len.toNat) :
    ∃ node, out.updated.extra.nodes.get out.borrowed.child = some node ∧
      node.tag = out.borrowed.output.tag ∧ node.children = #[] ∧ node.isExposed = false ∧
      ActiveWithin out.updated.extra out.borrowed.child .Write
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) := by
  rw [facts.extra]
  exact bool_written_data (CurrentCallPush.prepared_input input frames) {} out.source.base.raw positive out.borrowed facts.written

/-- Full Bool-child rights are retained by the actual initial Write and by the
physical writeUninit allocation update. -/
theorem bool_authority (facts : CurrentCallEntry.Facts out count) (positive : 0 < len.toNat) :
    OwnedOn (S05CompletedAncestryReadMutable.Authority out.updated.extra
      (S05ConcreteProtectedChildCompletion.extend (CurrentCallBoolProtection.returnCompletion out.source.base.raw)
        out.borrowed.child out.source.base.raw.returnPointer.grant)
      out.borrowed.output.global.protectedTags out.borrowed.child)
      (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) out.updated.extra.locations := by
  rw [facts.extra]
  exact bool_written_authority (CurrentCallPush.prepared_input input frames) {} out.source.base.raw positive out.borrowed

/-- The source rights refer to the same physical tree and completed ancestry
when source and Bool share their allocation. -/
theorem source_authority (facts : CurrentCallEntry.Facts out count) :
    let raw := out.source.base.raw
    let tree := if call.sourceId = call.returnId then out.updated.extra else raw.output.child.tree
    let completion := if call.sourceId = call.returnId then
      S05ConcreteProtectedChildCompletion.extend (CurrentCallBoolProtection.returnCompletion raw) out.borrowed.child raw.returnPointer.grant
      else S05ConcreteProtectedChildCompletion.extend raw.sourcePrecise.completion raw.child raw.sourcePointer.grant
    OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion out.borrowed.output.global.protectedTags raw.child)
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) tree.locations := by
  dsimp only
  rw [facts.extra]
  exact facts.written.sourceOwned
/-- The actual source leaf after both entry protectors and the initial Bool
Write, with one tree chosen by the actual allocation identity equality. -/
theorem source_data (facts : CurrentCallEntry.Facts out count) (positive : 0 < len.toNat) :
    let tree := if call.sourceId = call.returnId then out.updated.extra else out.source.base.raw.output.child.tree
    ∃ node, tree.nodes.get out.source.base.raw.child = some node ∧
      node.tag = out.source.base.raw.output.tag ∧ node.children = #[] ∧ node.isExposed = false ∧
      ActiveWithin tree out.source.base.raw.child .Write
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) := by
  dsimp only
  by_cases same : call.sourceId = call.returnId
  · rw [if_pos same,facts.extra]
    exact source_same_written_data (CurrentCallPush.prepared_input input frames) {} out.source.base.raw
      positive out.borrowed facts.written same
  · rw [if_neg same]
    exact source_initial_data facts positive

/-- The logical output global is exactly the actual postentry tracker global. -/
theorem current_tracker (_facts : CurrentCallEntry.Facts out count) :
    (out.machine count).borrowTracker = some ⟨out.borrowed.output.global,tracker.retagMode⟩ := by
  have outputEq : out.borrowed.output = CurrentCallTypedFnEntry.literal
      (CurrentCallBoolProtection.returnTree out.source.base.raw) out.source.base.raw.output.global
      out.source.base.raw.output.frame call.returnId out.room out.source.base.raw.returnPointer.value.provenance
      (UInt64.ofNat call.returnOffset) 1 := Except.ok.inj
    (out.borrowed.actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ out.room _ _ _))
  rw [outputEq]
  rfl

private theorem bool_global : out.borrowed.output.global =
    (registered out.source.base.raw.output.global out.source.base.raw.output.frame call.returnId out.room).1 := by
  have outputEq : out.borrowed.output = CurrentCallTypedFnEntry.literal
      (CurrentCallBoolProtection.returnTree out.source.base.raw) out.source.base.raw.output.global
      out.source.base.raw.output.frame call.returnId out.room out.source.base.raw.returnPointer.value.provenance
      (UInt64.ofNat call.returnOffset) 1 := Except.ok.inj
    (out.borrowed.actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ out.room _ _ _))
  exact congrArg GeneralBorrowForestFnEntry.Output.global outputEq

/-- Runtime, exact completed ancestry, order and finite callback headroom for
the actual Bool tree after the initial Write. -/
theorem bool_resources (facts : CurrentCallEntry.Facts out count) :
    DuplicatePrefixBorrowContract.RuntimeFacts out.updated.extra out.borrowed.output.global ∧
    Completes out.updated.extra
      (S05ConcreteProtectedChildCompletion.extend (CurrentCallBoolProtection.returnCompletion out.source.base.raw)
        out.borrowed.child out.source.base.raw.returnPointer.grant) ∧
    ParentTagOrder out.updated.extra ∧ out.updated.extra.nodes.size < 65536 ∧
    (S05ConcreteProtectedChildCompletion.extend (CurrentCallBoolProtection.returnCompletion out.source.base.raw)
      out.borrowed.child out.source.base.raw.returnPointer.grant).parents[out.borrowed.child.toNat]? =
        some (some out.source.base.raw.returnPointer.grant) := by
  have order := GeneralBorrowParentTagInvariant.nodes_frame out.borrowed.output.child.tree
    (CurrentCallBoolProtection.writeResult out.borrowed).tree facts.written.nodes out.borrowed.metadata.order
  have short : (CurrentCallBoolProtection.writeResult out.borrowed).tree.nodes.size < 65536 := by
    rw [facts.written.nodes]
    have budget := (CurrentCallBoolProtection.return_budget (CurrentCallPush.prepared_input input frames) {} out.source.base.raw).2.2
    have growth := out.borrowed.metadata.growth
    omega
  rw [facts.extra]
  exact ⟨facts.written.runtime,facts.written.completes,order,short,S05ConcreteProtectedChildCompletion.child_edge _ _ _⟩

/-- Source runtime uses the same current two-protector global as Bool, whether
its allocation coincides with Bool or remains physically separate. -/
theorem source_resources (facts : CurrentCallEntry.Facts out count) :
    let raw := out.source.base.raw
    let tree := if call.sourceId = call.returnId then out.updated.extra else raw.output.child.tree
    let completion := if call.sourceId = call.returnId then
      S05ConcreteProtectedChildCompletion.extend (CurrentCallBoolProtection.returnCompletion raw) out.borrowed.child raw.returnPointer.grant
      else S05ConcreteProtectedChildCompletion.extend raw.sourcePrecise.completion raw.child raw.sourcePointer.grant
    DuplicatePrefixBorrowContract.RuntimeFacts tree out.borrowed.output.global ∧ Completes tree completion ∧
      ParentTagOrder tree ∧ tree.nodes.size < 65536 := by
  dsimp only
  by_cases same : call.sourceId = call.returnId
  · rw [if_pos same,if_pos same]
    exact ⟨(bool_resources facts).1,(bool_resources facts).2.1,(bool_resources facts).2.2.1,(bool_resources facts).2.2.2.1⟩
  · rw [if_neg same,if_neg same]
    have registeredRuntime := (GeneralBorrowFnEntryRegistrationRuntime.prepare out.source.base.raw.output.child.tree
      out.source.base.raw.output.global out.source.base.raw.output.frame call.returnId out.room out.source.base.raw.runtime).2.2.2.1
    have runtime : DuplicatePrefixBorrowContract.RuntimeFacts out.source.base.raw.output.child.tree out.borrowed.output.global := by
      rw [bool_global]
      exact registeredRuntime
    have margin : out.source.base.raw.sourceAllocation.extra.nodes.size+16 < 65536 := by
      have present := out.source.base.raw.sourcePresent
      change Present (ActualWorld (CurrentCallPush.preparedMachine before frames)) call.sourceId out.source.base.raw.sourceAllocation at present
      simp only [Present,ActualWorld,Array.toList_map] at present
      obtain ⟨⟨oldId,entry⟩,member,equal⟩ := List.mem_map.mp present
      have allocationEq : entry.allocation = out.source.base.raw.sourceAllocation := (Prod.mk.inj equal).2
      rw [←allocationEq]
      exact (CurrentCallPush.prepared_input input frames).machine.resources.nodeRoom (oldId,entry) member
    have growth := out.source.base.raw.outputGrowth
    exact ⟨runtime,out.source.base.raw.completes,out.source.base.raw.outputOrder,by omega⟩

/-- The original return grant remains an actual stored node, retaining its
concrete stored tag or wildcard exposure after the initial Bool Write. -/
theorem original_return_node (facts : CurrentCallEntry.Facts out count) :
    ∃ node, out.updated.extra.nodes.get out.source.base.raw.returnPointer.grant = some node ∧
      (match out.source.base.raw.returnPointer.value.provenance with
      | .concrete _ tag => tag = node.tag | .wildcard => node.isExposed = true) := by
  obtain ⟨_,_,_,node,present,provenance⟩ := CurrentCallBoolProtection.return_ready
    (CurrentCallPush.prepared_input input frames) {} out.source.base.raw
  obtain ⟨next,nextAt,tag,_,hidden⟩ := out.borrowed.metadata.old out.source.base.raw.returnPointer.grant node present
  refine ⟨next,?_,?_⟩
  · rw [facts.extra,facts.written.nodes]
    exact nextAt
  · cases prov : out.source.base.raw.returnPointer.value.provenance with
    | concrete id pointerTag =>
      have old : pointerTag = node.tag := by simpa only [prov] using provenance
      exact old.trans tag.symm
    | wildcard =>
      simpa only [prov] using hidden.trans (by simpa only [prov] using provenance)

/-- A source protector in another allocation has no node in the current Bool
tree. Global freshness plus the actual constructor mapping proves absence. -/
theorem source_tag_absent (facts : CurrentCallEntry.Facts out count) (positive : 0 < len.toNat)
    (separate : call.sourceId ≠ call.returnId) : out.updated.extra.indexOfTag out.source.base.raw.output.tag = none := by
  have absent := source_tag_absent_bool (CurrentCallPush.prepared_input input frames) {} out.source.base.raw positive out.borrowed separate
  rw [facts.extra]
  unfold BorrowTree.indexOfTag
  have tags := congrArg BorrowTree.tagMapping (GeneralBorrowFreshReadFrame.frame out.borrowed.output.child.tree
    (.concrete out.borrowed.output.tag) (Size.ofBytes (UInt64.ofNat call.returnOffset)) (Size.ofBytes 1)
    .Write out.borrowed.output.global.protectedTags .VisitChildrenOfAccessed)
  change (CurrentCallBoolProtection.writeResult out.borrowed).tree.tagMapping = out.borrowed.output.child.tree.tagMapping at tags
  rw [tags]
  exact absent

end Facts

end
end DuplicatePrefix.CurrentCallEntryProtectionData
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallEntryProtectionData." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current entry protection dependency {dependency}"
