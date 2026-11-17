import duplicate_prefix.CurrentCallCheckpointLenControl
import duplicate_prefix.CurrentCallCheckpointLenMetadata
import duplicate_prefix.CurrentCallSpatialFutureCover
import duplicate_prefix.CurrentCallSpatialReleasedCover
namespace DuplicatePrefix.CurrentCallCheckpointLenRelease
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallPostEntryCheckpoint CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
variable {options remaining span len count place} (cp : Checkpoint options remaining span len count place)
def prepared := CurrentCallCheckpointLen.prepared cp

theorem source_id : (prepared cp).source.backing.id=cp.source.role.backing.id := by
  rw [←(prepared cp).source.id,(prepared cp).family]
  exact cp.source.role.id
private theorem replace_ids (rows : Array (AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind))
    (ids : (rows.toList.map Prod.fst).Nodup) (key : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) :
    (((rows.filter (fun row=>row.1!=key)).push (key,entry)).toList.map Prod.fst).Nodup := by
  let kept:=rows.toList.filter (fun row=>row.1!=key)
  have idsKept : (kept.map Prod.fst).Nodup := by
    simpa only [List.Nodup,List.filter_map,Function.comp_def,kept] using ids.filter (fun id=>id != key)
  simp only [Array.toList_push,Array.toList_filter,List.map_append]
  apply List.nodup_append.mpr
  refine ⟨idsKept,by simp,?_⟩
  intro a member b singleton same
  have equal : b=key:=by simpa using singleton
  subst b
  subst a
  obtain ⟨row,hit,rowId⟩:=List.mem_map.mp member
  have different:=(List.mem_filter.mp hit).2
  simp only [rowId,bne_self_eq_false,Bool.false_eq_true] at different


theorem source_allocation : (prepared cp).source.backing.allocation=(CurrentCallCheckpointLenControl.entry cp).allocation := by
  have ids : ((ActualWorld (CurrentCallCheckpointShared.machine cp)).toList.map Prod.fst).Nodup := by
    simp only [ActualWorld,Array.toList_map,List.map_map,Function.comp_def]
    exact replace_ids cp.machine.memory.live cp.ids cp.source.role.backing.id (CurrentCallCheckpointLenControl.entry cp)
  have actual : Present (ActualWorld (CurrentCallCheckpointShared.machine cp)) cp.source.role.backing.id (CurrentCallCheckpointLenControl.entry cp).allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    apply List.mem_map.mpr
    have currentLive : (CurrentCallCheckpointShared.machine cp).memory.live.find? (fun row=>row.1==cp.source.role.backing.id)=some (cp.source.role.backing.id,CurrentCallCheckpointLenControl.entry cp) :=
      StackPopRelease.lookup_commit_same _ _ _ _
    exact ⟨_,Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some currentLive),rfl⟩
  have backing := (prepared cp).source.backing.live
  rw [source_id cp] at backing
  exact (CandidateCurrentUniformOwnerWindow.same_id _ ids _ _ _ actual backing).symm

def registered := CurrentCallSpatialEntryRead.registeredTracker (prepared cp).source {} (prepared cp).room

def accessed := (prepared cp).source.backing.allocation.extra.performBorrowAccessRange (.concrete (prepared cp).readerNode.tag)
  (Size.ofBytes (UInt64.ofNat cp.offset)) (Size.ofBytes len) .Read (registered cp).global.protectedTags .VisitChildrenOfAccessed

def actual := (accessed cp).tree.newChild (Size.ofBytes (UInt64.ofNat cp.offset)) (.concrete (prepared cp).readerNode.tag)
  (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
  (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true

def helperFrame : FrameState:=({}:FrameState).addProtector (prepared cp).source.backing.id (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag

def future : MachineHooks.BorrowState:={registered cp with global:=(registered cp).global.endCall (helperFrame cp)}

theorem actual_eq : (actual cp).tree=CurrentCallCheckpointLenControl.borrowedTree cp := by
  unfold actual accessed
  rw [source_allocation cp,(prepared cp).readerTag]
  rfl

theorem held_eq : (registered cp).global=(CurrentCallCheckpointLenControl.held cp).global := by rfl

theorem future_eq : (future cp).global=(CurrentCallCheckpointLenControl.postTracker cp).global := by
  unfold future helperFrame
  rw [source_id cp]
  rfl

/-- The q bank is licensed on the ACTUAL helper-return heap, under only the
computed helper-endCall flags. The constructor's fixed completion extension
is shared by every saved row of each retained cell. -/
theorem future_cover {limits frame shape base}
    (returned : CurrentCallCheckpointLenControl.Returned cp limits frame shape base) :
    ∃context : CurrentCallSpatialCover.Context returned.machine,
      ∃current : RoleCover returned.machine (future cp) context .mut (UInt64.ofNat cp.offset).toNat len.toNat,
        current.family=(prepared cp).source.family ∧
        current.backing.allocation=(prepared cp).source.backing.allocation.setExtra (actual cp).tree ∧
        current.backing.id=(prepared cp).source.backing.id := by
  have nonzero : len≠0:=by intro zero;have positive:=cp.source.positive;rw [zero] at positive;cases positive
  obtain ⟨readDone,childDone,afterRuntime,capacity,growth,helper,lookup,caps,active,cells⟩:=CurrentCallCheckpointLen.operations cp
  obtain ⟨other,node,otherLookup,nodeAt,nodeTag,nodeParent,nodeHidden,vacant,oldGraph⟩:=CurrentCallCheckpointLenMetadata.graph (prepared cp).source rfl (prepared cp).runtime (prepared cp).distinct (prepared cp).short (prepared cp).nodeRoom cp.source.tag cp.source.grant (prepared cp).reader (prepared cp).readerNode (prepared cp).concrete (prepared cp).tagged (prepared cp).readerAt (prepared cp).readerEdge (prepared cp).hidden (prepared cp).unheld (prepared cp).room (UInt64.ofNat cp.offset) len rfl rfl nonzero (prepared cp).bounds (prepared cp).readable .VisitChildrenOfAccessed
  have same : other=helper:=Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  obtain ⟨other,otherLookup,leaf,oldFields⟩:=CurrentCallCheckpointLenMetadata.frame (prepared cp).source rfl (prepared cp).runtime (prepared cp).distinct (prepared cp).short (prepared cp).nodeRoom cp.source.tag cp.source.grant (prepared cp).reader (prepared cp).readerNode (prepared cp).concrete (prepared cp).tagged (prepared cp).readerAt (prepared cp).readerEdge (prepared cp).hidden (prepared cp).unheld (prepared cp).room (UInt64.ofNat cp.offset) len rfl rfl nonzero (prepared cp).bounds (prepared cp).readable .VisitChildrenOfAccessed
  have same : other=helper:=Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  obtain ⟨contract,readRuntime,parents⟩:=CurrentCallSpatialLenAssociatedRead.prepare
    (prepared cp).source rfl (prepared cp).runtime (prepared cp).distinct (prepared cp).short
    cp.source.tag cp.source.grant (prepared cp).reader (prepared cp).readerNode
    (prepared cp).concrete (prepared cp).tagged (prepared cp).readerAt (prepared cp).readerEdge (prepared cp).hidden (prepared cp).unheld
    (prepared cp).room (UInt64.ofNat cp.offset) len rfl rfl nonzero (prepared cp).bounds (prepared cp).readable .VisitChildrenOfAccessed
  have currentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (actual cp).tree (registered cp).global:=afterRuntime
  obtain ⟨futureRuntime,_,_⟩:=GeneralBorrowHiddenProtectorDropRuntime.end_call (actual cp).tree (registered cp).global currentRuntime
    (prepared cp).source.backing.id (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag helper node nodeAt nodeTag nodeHidden
  have live : Present (ActualWorld returned.machine) (prepared cp).source.backing.id ((prepared cp).source.backing.allocation.setExtra (actual cp).tree) := by
    rw [source_id cp,source_allocation cp,actual_eq cp]
    exact CurrentCallCheckpointLenControl.source_present cp returned
  have leafRoots : (actual cp).tree.roots=(accessed cp).tree.roots := leaf.roots
  have readRoots : (accessed cp).tree.roots=(prepared cp).source.backing.allocation.extra.roots := contract.roots
  have rootSlots : ∀(position : Nat) (root : UniIndex),(prepared cp).source.backing.allocation.extra.roots[position]?=some root→(actual cp).tree.roots[position]?=some root := by
    intro position root atRoot
    rw [leafRoots,readRoots]
    exact atRoot
  have futureRuntime' : DuplicatePrefixBorrowContract.RuntimeFacts (actual cp).tree (future cp).global := futureRuntime
  have oldFields' : ∀index old,(prepared cp).source.backing.allocation.extra.nodes.get index=some old→∃changed,
      (actual cp).tree.nodes.get index=some changed ∧changed.tag=old.tag ∧changed.parent=old.parent ∧
      changed.isExposed=old.isExposed ∧changed.defaultInitialPermission=old.defaultInitialPermission := oldFields
  have cells' : ∀(i : Fin (prepared cp).source.backing.cells.size) (_overlap : CurrentCallSpatialSourceCover.Active (prepared cp).source i)
      (lower upper : UInt64),(UInt64.ofNat cp.offset).toNat≤lower.toNat→upper.toNat≤(UInt64.ofNat cp.offset).toNat+len.toNat→
      (prepared cp).source.backing.cells[i].offset≤lower.toNat→upper.toNat≤(prepared cp).source.backing.cells[i].offset+(prepared cp).source.backing.cells[i].length→
      ParentInterpretation (actual cp).tree (S05ConcreteProtectedChildCompletion.extend (prepared cp).source.backing.cells[i].completion helper (prepared cp).reader) ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority (actual cp).tree (S05ConcreteProtectedChildCompletion.extend (prepared cp).source.backing.cells[i].completion helper (prepared cp).reader)
        (future cp).global.protectedTags cp.source.grant) lower upper (actual cp).tree.locations := cells
  let updates:=CurrentCallSpatialFutureCover.updates (post:=returned.machine) (next:=future cp) (tree:=(actual cp).tree)
    (tag:=cp.source.tag) (parent:=cp.source.grant) (reader:=helper) (constructorParent:=(prepared cp).reader)
    (prepared cp).source live (by rfl) capacity rootSlots oldFields' vacant futureRuntime'
    (prepared cp).concrete (prepared cp).tagged cells'
  exact ⟨CurrentCallSpatialSourceCover.context (prepared cp).source live updates,
    CurrentCallSpatialSourceCover.assemble (prepared cp).source live updates (prepared cp).source.id,rfl,rfl,rfl⟩

/-- ONE actual helper release uses the current Strong flags. Its saved-row
certificate retains every fixed future cell bank together. -/
theorem release {limits frame shape base}
    (returned : CurrentCallCheckpointLenControl.Returned cp limits frame shape base) :
    let result := (actual cp).tree.releaseProtector (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag (registered cp).global.protectedTags
    result.status=.Released ∧DuplicatePrefixBorrowContract.RuntimeFacts result.tree (registered cp).global ∧
      result.tree={(actual cp).tree with locations:=result.tree.locations} ∧result.tree.locations.size=(actual cp).tree.locations.size ∧
      ∃context : CurrentCallSpatialCover.Context returned.machine,
        ∃current : RoleCover returned.machine (future cp) context .mut (UInt64.ofNat cp.offset).toNat len.toNat,
          current.backing.allocation=(prepared cp).source.backing.allocation.setExtra (actual cp).tree ∧
          current.backing.id=(prepared cp).source.backing.id ∧
          current.backing.allocation.extra=(actual cp).tree ∧current.family=(prepared cp).source.family ∧
          S05CurrentReleaseIterator.Rows (fun range location=>∃original∈current.backing.allocation.extra.locations.entries.toList,
            original.range=range ∧CurrentCallSpatialRows.Frame current original.data location) result.tree.locations := by
  obtain ⟨context,Q,family,allocation,idEq⟩:=future_cover cp returned
  have treeEq : Q.backing.allocation.extra=(actual cp).tree:=congrArg Allocation.extra allocation
  have nonzero : len≠0:=by intro zero;have positive:=cp.source.positive;rw [zero] at positive;cases positive
  obtain ⟨readDone,childDone,afterRuntime,capacity,growth,helper,lookup,caps,active,cells⟩:=CurrentCallCheckpointLen.operations cp
  obtain ⟨other,node,otherLookup,nodeAt,nodeTag,nodeParent,nodeHidden,vacant,oldGraph⟩:=CurrentCallCheckpointLenMetadata.graph (prepared cp).source rfl (prepared cp).runtime (prepared cp).distinct (prepared cp).short (prepared cp).nodeRoom cp.source.tag cp.source.grant (prepared cp).reader (prepared cp).readerNode (prepared cp).concrete (prepared cp).tagged (prepared cp).readerAt (prepared cp).readerEdge (prepared cp).hidden (prepared cp).unheld (prepared cp).room (UInt64.ofNat cp.offset) len rfl rfl nonzero (prepared cp).bounds (prepared cp).readable .VisitChildrenOfAccessed
  have same : other=helper:=Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  obtain ⟨other,otherLookup,leaf,oldFields⟩:=CurrentCallCheckpointLenMetadata.frame (prepared cp).source rfl (prepared cp).runtime (prepared cp).distinct (prepared cp).short (prepared cp).nodeRoom cp.source.tag cp.source.grant (prepared cp).reader (prepared cp).readerNode (prepared cp).concrete (prepared cp).tagged (prepared cp).readerAt (prepared cp).readerEdge (prepared cp).hidden (prepared cp).unheld (prepared cp).room (UInt64.ofNat cp.offset) len rfl rfl nonzero (prepared cp).bounds (prepared cp).readable .VisitChildrenOfAccessed
  have same : other=helper:=Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  obtain ⟨_,_,_,_,_,_,_,_,⟨qOld,qOldAt,qOldTag,qOldParent,qOldHidden⟩,_,_⟩:=CurrentCallCheckpointShared.metadata cp
  have qInitial : (prepared cp).source.backing.allocation.extra.nodeAt cp.source.grant=some qOld := by
    rw [(prepared cp).tree];exact qOldAt
  obtain ⟨qNode,qAt,qTag,qParent,qHidden⟩:=oldGraph _ _ qInitial
  obtain ⟨rNode,rAt,rTag,rParent,rHidden⟩:=oldGraph _ _ (prepared cp).readerAt
  have currentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (actual cp).tree (registered cp).global:=afterRuntime
  have concrete : Q.family.value.provenance=.concrete Q.backing.id cp.source.tag := by
    rw [family,idEq];exact (prepared cp).concrete
  have tagged : Q.backing.allocation.extra.indexOfTag cp.source.tag=some cp.source.grant := by
    rw [treeEq]
    have mapped:=currentRuntime.formed.allocator.nodeTags _ _ qAt
    have tagEq:=qTag.trans (qOldTag.trans cp.source.nodeTag)
    rw [tagEq] at mapped
    exact mapped
  have hAt : Q.backing.allocation.extra.nodeAt helper=some node:=by rw [treeEq];exact nodeAt
  have rAt' : Q.backing.allocation.extra.nodeAt (prepared cp).reader=some rNode:=by rw [treeEq];exact rAt
  have unheld : (registered cp).global.protectedTags.contains rNode.tag=false := by
    rw [rTag]
    obtain ⟨_,_,_,_,nodeFresh,_⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare (prepared cp).source.backing.allocation.extra
      (CurrentCallCheckpointShared.tracker cp).global {} (prepared cp).source.backing.id (prepared cp).room (prepared cp).runtime
    have different:=nodeFresh ((prepared cp).reader,(prepared cp).readerNode)
      (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get _ _ _).mpr (prepared cp).readerAt))
    have flags:=ProtectorInsertion.contains_other (CurrentCallCheckpointShared.tracker cp).global.protectedTags
      (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag (prepared cp).readerNode.tag .StrongProtector different
    exact flags.trans (prepared cp).unheld
  have currentRuntime' : DuplicatePrefixBorrowContract.RuntimeFacts Q.backing.allocation.extra (registered cp).global:=by rw [treeEq];exact currentRuntime
  have distinct : Q.backing.allocation.extra.roots.toList.Nodup := by
    rw [treeEq]
    have roots : (actual cp).tree.roots=(accessed cp).tree.roots:=leaf.roots
    obtain ⟨contract,_,_⟩:=CurrentCallSpatialLenAssociatedRead.prepare (prepared cp).source rfl (prepared cp).runtime (prepared cp).distinct (prepared cp).short
      cp.source.tag cp.source.grant (prepared cp).reader (prepared cp).readerNode (prepared cp).concrete (prepared cp).tagged (prepared cp).readerAt
      (prepared cp).readerEdge (prepared cp).hidden (prepared cp).unheld (prepared cp).room (UInt64.ofNat cp.offset) len rfl rfl nonzero (prepared cp).bounds (prepared cp).readable .VisitChildrenOfAccessed
    have readRoots : (accessed cp).tree.roots=(prepared cp).source.backing.allocation.extra.roots:=contract.roots
    rw [roots,readRoots];exact (prepared cp).distinct
  have short : Q.backing.allocation.extra.nodes.size<65536 := by
    rw [treeEq]
    have sharedGrowth:=(CurrentCallCheckpointShared.operation cp).2.2.2.2.1
    have budget:=cp.source.nodes
    have growth' : (actual cp).tree.nodes.size≤(prepared cp).source.backing.allocation.extra.nodes.size+1:=growth
    rw [(prepared cp).tree] at growth'
    change (CurrentCallCheckpointShared.role cp).backing.allocation.extra.nodes.size+6<65536 at budget
    omega
  have fit : (UInt64.ofNat cp.offset).toNat+len.toNat<2^64:=Nat.lt_of_le_of_lt (prepared cp).bounds (prepared cp).source.backing.allocation.extra.locations.size.bytes.toNat_lt
  have noWrap : (UInt64.ofNat cp.offset+len).toNat=(UInt64.ofNat cp.offset).toNat+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt fit]
  have positive : (UInt64.ofNat cp.offset).toNat<(UInt64.ofNat cp.offset+len).toNat := by rw [noWrap];have p:=cp.source.positive;omega
  have activity : GeneralBorrowFreshActiveWithin.ActiveWithin Q.backing.allocation.extra helper .Read (UInt64.ofNat cp.offset) (UInt64.ofNat cp.offset+len):=by rw [treeEq];exact active
  have readable : OwnedOn (fun location=>Nonempty (DuplicatePrefixNormalKind.Capability Q.backing.allocation.extra location (registered cp).global.protectedTags helper .Read))
      (UInt64.ofNat cp.offset) (UInt64.ofNat cp.offset+len) Q.backing.allocation.extra.locations := by
    rw [treeEq]
    intro cursor valid positive lower upper
    exact (caps cursor valid positive lower upper).2
  obtain ⟨done,shape,runtime,capacity,rows⟩:=CurrentCallSpatialLenRelease.release Q rfl (registered cp).global currentRuntime' distinct short
    cp.source.tag cp.source.grant helper node concrete tagged hAt (prepared cp).reader rNode rAt' nodeParent
    (rParent.trans (prepared cp).readerEdge) nodeHidden (rHidden.trans (prepared cp).hidden) unheld
    (by unfold future helperFrame;rw [←idEq,nodeTag]) (UInt64.ofNat cp.offset) len rfl rfl positive noWrap activity readable
  have tagEq : node.tag=(CurrentCallCheckpointShared.tracker cp).global.nextPointerTag:=nodeTag
  rw [treeEq,tagEq] at done shape runtime capacity rows
  exact ⟨done,runtime,shape,capacity,context,Q,allocation,idEq,treeEq,family,by simpa only [treeEq] using rows⟩

/-- Exact certificate consumed by the common C-free LenReturn leaf. -/
theorem completed {limits frame shape base}
    (returned : CurrentCallCheckpointLenControl.Returned cp limits frame shape base) :
    ((CurrentCallCheckpointLenControl.borrowedTree cp).releaseProtector
      (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
      (CurrentCallCheckpointLenControl.held cp).global.protectedTags).status=.Released := by
  have done : ((actual cp).tree.releaseProtector (CurrentCallCheckpointShared.tracker cp).global.nextPointerTag
    (registered cp).global.protectedTags).status=.Released := (release cp returned).1
  rw [actual_eq cp,held_eq cp] at done
  exact done

end
end DuplicatePrefix.CurrentCallCheckpointLenRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointLenRelease" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved checkpoint Len release dependency {dependency}"
