import duplicate_prefix.CurrentCallCheckpointAcceptedBoolFrame
import duplicate_prefix.CurrentCallCheckpointAsMutControl
import duplicate_prefix.CurrentCallCheckpointAsMutReturn
import duplicate_prefix.CurrentCallCheckpointMutableCurrent
import duplicate_prefix.CurrentCallCheckpointBoolInstall
import duplicate_prefix.CurrentCallCheckpointAsMutFacts

namespace DuplicatePrefix.CurrentCallCheckpointAcceptedBoolCurrent
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallPostEntryCheckpoint CurrentCallCheckpointRoot3 GeneralRangeMapOrigins
open S05ConcreteProtectedChildCompletion S05CompletedAncestryReadMutable
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
variable {options remaining span len count place limits}
    {cp : Checkpoint options remaining span len count place}
    (out : Output cp limits) (done : CurrentCallCheckpointDefaultControl.Done out)
    (seed : CurrentCallCheckpointAsMutControl.Helper out done)

theorem parent_allocation :
    (CurrentCallCheckpointMutable.prepared cp out.result out.source).role.backing.allocation=
      (CurrentCallCheckpointAsMutControl.entry out).allocation := by
  rw [(CurrentCallCheckpointMutable.prepared cp out.result out.source).allocation,out.source.allocation]
  change ((CurrentCallCheckpointLenControl.entry cp).allocation.setExtra (CurrentCallCheckpointLenControl.releasedTree cp)).setExtra
    (CurrentCallCheckpointMutable.tree cp out.result out.source)=_
  rw [CurrentCallCheckpointAsMutControl.p_tree out]
  rfl

theorem helper_present : Present (ActualWorld seed.machine)
    (CurrentCallCheckpointMutable.prepared cp out.result out.source).role.backing.id
    ((CurrentCallCheckpointMutable.prepared cp out.result out.source).role.backing.allocation.setExtra
      (CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree) := by
  have actual := seed.live
  rw [CurrentCallCheckpointAsMutControl.helper_output out done seed] at actual
  have member := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some actual)
  simp only [Present,ActualWorld,Array.toList_map]
  rw [(CurrentCallCheckpointMutable.prepared cp out.result out.source).id,parent_allocation out]
  exact List.mem_map.mpr ⟨_,member,rfl⟩

include done seed in
/-- The current helper world supplies physical source capabilities for Bool
framing, without selecting a whole-span logical completion. -/
theorem source_normal :
    ∃child node,(CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree.indexOfTag
        (CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag=some child ∧
      (CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree.nodeAt child=some node ∧
      node.tag=(CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag ∧node.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree child .Write
        (UInt64.ofNat cp.offset) (UInt64.ofNat cp.offset+len) ∧
      OwnedOn (fun location=>Nonempty (DuplicatePrefixBorrowAuthorization.Normal
        (CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree location
        (CurrentCallCheckpointMutable.sOutput cp out.result out.source).global.protectedTags child))
        (UInt64.ofNat cp.offset) (UInt64.ofNat cp.offset+len)
        (CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree.locations := by
  let next : MachineHooks.BorrowState := {CurrentCallCheckpointMutable.next cp out.result out.source with
    global:=(CurrentCallCheckpointMutable.sOutput cp out.result out.source).global}
  obtain ⟨ctx,role,allocation,id,family⟩ := CurrentCallCheckpointMutableCurrent.cover cp out.result out.source seed.machine next
    (helper_present out done seed) rfl rfl
  obtain ⟨child,node,mapped,nodeAt,nodeTag,hidden,active,roots⟩ := CurrentCallCheckpointMutableCurrent.facets cp out.result out.source
  have treeEq := congrArg Allocation.extra allocation
  dsimp only [Allocation.setExtra,Allocation.mapExtra] at treeEq
  have concrete : role.family.value.provenance=.concrete role.backing.id (CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag := by
    rw [family,id]
    rfl
  have roleMapped : role.backing.allocation.extra.indexOfTag (CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag=some child := by rw [treeEq];exact mapped
  have runtime := (CurrentCallCheckpointMutable.s_operation cp out.result out.source).2.2.2.1
  have roleRuntime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra next.global := by rw [treeEq];exact runtime
  have bounds := (CurrentCallCheckpointMutable.prepared cp out.result out.source).bounds
  have capacity := (CurrentCallCheckpointMutable.s_operation cp out.result out.source).2.2.2.2.1
  change (CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree.locations.size=
    (CurrentCallCheckpointMutable.prepared cp out.result out.source).role.backing.allocation.extra.locations.size at capacity
  have roleBounds : (UInt64.ofNat cp.offset).toNat+len.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat := by rw [treeEq,capacity];exact bounds
  have normal := CurrentCallCheckpointMutableBoolFrame.spatial_normal role roleRuntime
    (CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag child concrete roleMapped
    (UInt64.ofNat cp.offset) len (CurrentCallCheckpointShared.start_eq cp) rfl roleBounds
  rw [treeEq] at normal
  exact ⟨child,node,mapped,nodeAt,nodeTag,hidden,active,normal⟩


/-- SAME-allocation Bool rights and activity are retained on the exact real
AsMut release tree. All source premises are derived from its actual S cover. -/
theorem released_same (same : cp.output.id=cp.source.role.backing.id) :
    ∃parent child,
      (CurrentCallCheckpointMutable.prepared cp out.result out.source).role.backing.allocation.extra.indexOfTag
        (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag=some parent ∧
      (CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree.indexOfTag
        (CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag=some child ∧
      ParentInterpretation (CurrentCallCheckpointAsMutReturn.releasedTree seed)
        (extend (extend out.target.current.window.precise.completion parent cp.source.grant) child parent) ∧
      OwnedOn (Authority (CurrentCallCheckpointAsMutReturn.releasedTree seed)
        (extend (extend out.target.current.window.precise.completion parent cp.source.grant) child parent)
        (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags out.target.current.window.pointer.grant)
        out.target.current.physical.offset (out.target.current.physical.offset+1) (CurrentCallCheckpointAsMutReturn.releasedTree seed).locations ∧
      (∃node,(CurrentCallCheckpointAsMutReturn.releasedTree seed).nodeAt out.target.current.window.pointer.grant=some node ∧
        node.tag=out.target.current.node.tag ∧node.parent=out.target.current.node.parent ∧node.children=out.target.current.node.children ∧
        node.isExposed=out.target.current.node.isExposed) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallCheckpointAsMutReturn.releasedTree seed)
        out.target.current.window.pointer.grant .Write out.target.current.physical.offset (out.target.current.physical.offset+1) := by
  obtain ⟨child,node,mapped,nodeAt,nodeTag,hidden,activity,normal⟩ := source_normal out done seed
  obtain ⟨parent,parentMapped,parents,owned,facets,active⟩ := CurrentCallCheckpointAcceptedBoolFrame.released_same cp out.result out.source out.target
    same child node mapped nodeAt hidden nodeTag activity normal
  have outputEq := CurrentCallCheckpointAsMutControl.helper_output out done seed
  have treeEq : CurrentCallCheckpointAsMutReturn.releasedTree seed=
      ((CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree.releaseProtector
        (CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag
        (CurrentCallCheckpointMutable.sOutput cp out.result out.source).global.protectedTags).tree := by
    unfold CurrentCallCheckpointAsMutReturn.releasedTree
    rw [outputEq]
  have flagsEq : (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags=
      ((CurrentCallCheckpointMutable.sOutput cp out.result out.source).global.endCall
        (CurrentCallCheckpointMutable.sOutput cp out.result out.source).frame).protectedTags := by
    change (seed.output.global.endCall seed.output.frame).protectedTags=_
    rw [outputEq]
  rw [treeEq,flagsEq]
  exact ⟨parent,child,parentMapped,mapped,parents,owned,facets,active⟩


private theorem extend_edges {old next : BorrowTree} {C : Completion} {global : GlobalState}
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts old global)
    (parents : ParentInterpretation old C) (child parent : UniIndex) (node : TreeNode)
    (present : next.nodes.get child=some node)
    (fresh : global.nextPointerTag.value.toNat≤node.tag.value.toNat)
    (metadata : ∀query oldNode,old.nodes.get query=some oldNode→∃nextNode,next.nodes.get query=some nextNode ∧nextNode.tag=oldNode.tag ∧
      nextNode.parent=oldNode.parent ∧nextNode.isExposed=oldNode.isExposed ∧nextNode.defaultInitialPermission=oldNode.defaultInitialPermission) :
    ∀(query origin : UniIndex),C.parents[query.toNat]?=some (some origin)→(extend C child parent).parents[query.toNat]?=some (some origin) := by
  have vacant : old.nodes.get child=none := by
    cases atOld : old.nodes.get child with
    | none=>rfl
    | some previous=>
      obtain ⟨changed,changedAt,changedTag,_⟩:=metadata child previous atOld
      have eq:=Option.some.inj (changedAt.symm.trans present)
      have older:=GeneralBorrowParentTagInvariant.parent_below_fresh _ _ runtime child previous atOld
      have numeric:=UInt64.lt_iff_toNat_lt.mp older
      rw [←changedTag,eq] at numeric
      omega
  exact (checkpoint_bool_rule "CurrentCallCheckpointSharedBoolFrame.edge_extend") parents child parent vacant

/-- Real P metadata, including root/default-permission fields, survives the
actual Strong S and release. This is the old-allocation licence transport. -/
theorem metadata_same (same : cp.output.id=cp.source.role.backing.id) :
    (∀query old,out.target.current.window.allocation.extra.nodes.get query=some old→∃next,
      (CurrentCallCheckpointAsMutReturn.releasedTree seed).nodes.get query=some next ∧next.tag=old.tag ∧next.parent=old.parent ∧
        next.isExposed=old.isExposed ∧next.defaultInitialPermission=old.defaultInitialPermission) ∧
    (CurrentCallCheckpointAsMutReturn.releasedTree seed).locations.size=out.target.current.window.allocation.extra.locations.size ∧
    (CurrentCallCheckpointAsMutReturn.releasedTree seed).roots=out.target.current.window.allocation.extra.roots ∧
    (CurrentCallCheckpointAsMutReturn.releasedTree seed).nodes.size<65536 := by
  obtain ⟨parent,mapped,parents,owned,facets,active,capacity,roots,growth,metadata⟩ :=
    CurrentCallCheckpointAcceptedBoolFrame.default_same cp out.result out.source out.target same
  obtain ⟨_,_,_,runtime,sCapacity,sGrowth,child,lookup,oldRoots,sMetadata,childNode⟩ :=
    CurrentCallCheckpointMutable.s_operation cp out.result out.source
  change (CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree.locations.size=
    (CurrentCallCheckpointMutable.prepared cp out.result out.source).role.backing.allocation.extra.locations.size at sCapacity
  have pTree := congrArg Allocation.extra (CurrentCallCheckpointMutable.prepared cp out.result out.source).allocation
  dsimp only [Allocation.setExtra,Allocation.mapExtra] at pTree
  have alias : CurrentCallCheckpointMutable.tree cp out.result out.source=CurrentCallCheckpointAcceptedBoolFrame.tree cp out.result out.source:=rfl
  have sourceAllocation := CurrentCallCheckpointAcceptedBoolFrame.allocation_same cp out.result out.source out.target same
  have releaseShape := GeneralBorrowStructuralReleaseGeometryFrame.release
    (CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree
    (CurrentCallCheckpointMutable.sOutput cp out.result out.source).global.protectedTags
    (CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag
  have outputEq:=CurrentCallCheckpointAsMutControl.helper_output out done seed
  have treeEq : CurrentCallCheckpointAsMutReturn.releasedTree seed=
      ((CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree.releaseProtector
        (CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag
        (CurrentCallCheckpointMutable.sOutput cp out.result out.source).global.protectedTags).tree:=by
    unfold CurrentCallCheckpointAsMutReturn.releasedTree;rw [outputEq]
  have nodesEq := congrArg BorrowTree.nodes releaseShape
  have rootsEq := congrArg BorrowTree.roots releaseShape
  have sCap := (CurrentCallCheckpointMutableCurrent.release cp out.result out.source seed.machine (helper_present out done seed)).2.2.2
  have releasedShort := CurrentCallCheckpointMutableCurrent.short cp out.result out.source
  have sRoots := (CurrentCallCheckpointMutableCurrent.facets cp out.result out.source)
  obtain ⟨_,_,_,_,_,_,_,actualRoots⟩:=sRoots
  refine ⟨?_,?_,?_,?_⟩
  · intro query previous atPrevious
    rw [sourceAllocation] at atPrevious
    obtain ⟨middle,middleAt,middleTag,middleParent,middleHidden,middleDefault⟩:=metadata query previous atPrevious
    have atP : (CurrentCallCheckpointMutable.prepared cp out.result out.source).role.backing.allocation.extra.nodes.get query=some middle:=by
      rw [pTree,alias];exact middleAt
    obtain ⟨next,nextAt,nextTag,nextParent,nextHidden,nextDefault⟩:=sMetadata query middle atP
    refine ⟨next,?_,nextTag.trans middleTag,nextParent.trans middleParent,nextHidden.trans middleHidden,nextDefault.trans middleDefault⟩
    rw [treeEq,nodesEq];exact nextAt
  · rw [treeEq,sCap,sCapacity,pTree,alias,capacity,sourceAllocation]
  · rw [treeEq,rootsEq,actualRoots,pTree,alias,roots,sourceAllocation]
  · rw [treeEq]
    change (((CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree.releaseProtector
      (CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag
      (CurrentCallCheckpointMutable.sOutput cp out.result out.source).global.protectedTags).tree.nodes.data.size)<65536
    rw [nodesEq]
    exact releasedShort


/-- Actual release runtime followed by the actual hidden S endCall. -/
theorem runtime : DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallCheckpointAsMutReturn.releasedTree seed)
    (CurrentCallCheckpointAsMutReturn.postTracker seed).global := by
  obtain ⟨child,node,mapped,nodeAt,nodeTag,hidden,activity,roots⟩ := CurrentCallCheckpointMutableCurrent.facets cp out.result out.source
  obtain ⟨completed,current,shape,capacity⟩ := CurrentCallCheckpointMutableCurrent.release cp out.result out.source seed.machine (helper_present out done seed)
  have nodes := congrArg BorrowTree.nodes shape
  have afterAt : (((CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree.releaseProtector
      (CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag
      (CurrentCallCheckpointMutable.sOutput cp out.result out.source).global.protectedTags).tree).nodeAt child=some node := by
    change (((CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree.releaseProtector
      (CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag
      (CurrentCallCheckpointMutable.sOutput cp out.result out.source).global.protectedTags).tree).nodes.get child=some node
    rw [nodes]
    exact nodeAt
  have retained := GeneralBorrowHiddenProtectorDropRuntime.end_call _ _ current
    (CurrentCallCheckpointMutable.prepared cp out.result out.source).role.backing.id
    (CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag child node afterAt nodeTag hidden
  have outputEq:=CurrentCallCheckpointAsMutControl.helper_output out done seed
  change DuplicatePrefixBorrowContract.RuntimeFacts
    (seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags).tree
    (seed.output.global.endCall seed.output.frame)
  rw [outputEq]
  exact retained.1


def parent : UniIndex:=((CurrentCallCheckpointMutable.prepared cp out.result out.source).role.backing.allocation.extra.indexOfTag
  (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag).getD ⟨0⟩
def child : UniIndex:=((CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree.indexOfTag
  (CurrentCallCheckpointMutable.sOutput cp out.result out.source).tag).getD ⟨0⟩
def bank : Completion:=if cp.output.id=cp.source.role.backing.id then
  extend (extend out.target.current.window.precise.completion (parent out) cp.source.grant) (child out) (parent out)
  else out.target.current.window.precise.completion

/-- All old Bool parent-map edges survive the two genuinely fresh slots. -/
theorem edges_same (same : cp.output.id=cp.source.role.backing.id) :
    ∀(query origin : UniIndex),out.target.current.window.precise.completion.parents[query.toNat]?=some (some origin)→
      (bank out).parents[query.toNat]?=some (some origin) := by
  let p:=CurrentCallCheckpointMutable.prepared cp out.result out.source
  have positive:=cp.source.positive
  obtain ⟨i,cell⟩:=p.role.covered (p.role.backing.id,cp.offset) ⟨rfl,Nat.le_refl _,by omega⟩
  let overlap : CurrentCallSpatialSourceCover.Active p.role i:=⟨_,⟨rfl,Nat.le_refl _,by omega⟩,cell⟩
  obtain ⟨pNode,pAt,pMapped,pBinding⟩:=(p.role.roles i overlap).binding
  have concrete:=CurrentCallCheckpointMutable.p_provenance cp out.result out.source
  change (match p.role.family.value.provenance with | .concrete id tag=>id=p.role.family.allocation ∧tag=pNode.tag | .wildcard=>pNode.isExposed=true) at pBinding
  rw [concrete] at pBinding
  have pTag : pNode.tag=(CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag:=pBinding.2.symm
  have pLookup : p.role.backing.allocation.extra.indexOfTag (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag=some (p.role.roles i overlap).grant:=by rw [←pTag];exact pMapped
  have pIndex : parent out=(p.role.roles i overlap).grant:=by unfold parent;rw [pLookup];rfl
  obtain ⟨other,mapped,parents,owned,facets,active,capacity,roots,growth,metadata⟩ :=
    CurrentCallCheckpointAcceptedBoolFrame.default_same cp out.result out.source out.target same
  have pTree:=congrArg Allocation.extra p.allocation
  dsimp only [Allocation.setExtra,Allocation.mapExtra] at pTree
  have alias : CurrentCallCheckpointMutable.tree cp out.result out.source=CurrentCallCheckpointAcceptedBoolFrame.tree cp out.result out.source:=rfl
  have otherLookup : p.role.backing.allocation.extra.indexOfTag (CurrentCallCheckpointLenControl.postTracker cp).global.nextPointerTag=some other:=by rw [pTree,alias];exact mapped
  have otherEq : other=parent out:=by rw [pIndex];exact Option.some.inj (otherLookup.symm.trans pLookup)
  subst other
  have allocation:=CurrentCallCheckpointAcceptedBoolFrame.allocation_same cp out.result out.source out.target same
  have oldParents : ParentInterpretation out.target.current.window.allocation.extra out.target.current.window.precise.completion:=out.target.current.window.parents
  have metaP : ∀query old,out.target.current.window.allocation.extra.nodes.get query=some old→∃next,p.role.backing.allocation.extra.nodes.get query=some next ∧
      next.tag=old.tag ∧next.parent=old.parent ∧next.isExposed=old.isExposed ∧next.defaultInitialPermission=old.defaultInitialPermission:=by
    intro query old atOld
    rw [allocation] at atOld
    rw [pTree,alias]
    exact metadata query old atOld
  have pAtCanonical : p.role.backing.allocation.extra.nodes.get (parent out)=some pNode:=by rw [pIndex];exact pAt
  have first := extend_edges out.target.current.runtime oldParents (parent out) cp.source.grant pNode pAtCanonical
    (by rw [pTag];exact Nat.le_refl _) metaP
  have nextParents : ParentInterpretation p.role.backing.allocation.extra
      (extend out.target.current.window.precise.completion (parent out) cp.source.grant):=by rw [pTree,alias];exact parents
  obtain ⟨s,sNode,sMapped,sAt,sTag,sHidden,sActive,sRoots⟩:=CurrentCallCheckpointMutableCurrent.facets cp out.result out.source
  have sIndex : child out=s:=by unfold child;rw [sMapped];rfl
  have sAtCanonical : (CurrentCallCheckpointMutable.sOutput cp out.result out.source).child.tree.nodes.get (child out)=some sNode:=by rw [sIndex];exact sAt
  obtain ⟨_,_,_,_,_,_,_,_,_,sMetadata,_⟩:=CurrentCallCheckpointMutable.s_operation cp out.result out.source
  have second := extend_edges p.runtime nextParents (child out) (parent out) sNode sAtCanonical
    (by rw [sTag];exact Nat.le_refl _) sMetadata
  intro query origin edge
  change (if cp.output.id=cp.source.role.backing.id then
    extend (extend out.target.current.window.precise.completion (parent out) cp.source.grant) (child out) (parent out)
    else out.target.current.window.precise.completion).parents[query.toNat]?=some (some origin)
  rw [ite_eq_left same]
  exact second query origin (first query origin edge)


/-- Fixed actual P/S indices identify the one Bool bank, independently of
any logical source-cell completion choice. -/
theorem same_raw (same : cp.output.id=cp.source.role.backing.id) :
    ParentInterpretation (CurrentCallCheckpointAsMutReturn.releasedTree seed) (bank out) ∧
    OwnedOn (Authority (CurrentCallCheckpointAsMutReturn.releasedTree seed) (bank out)
      (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags out.target.current.window.pointer.grant)
      out.target.current.physical.offset (out.target.current.physical.offset+1) (CurrentCallCheckpointAsMutReturn.releasedTree seed).locations ∧
    (∃node,(CurrentCallCheckpointAsMutReturn.releasedTree seed).nodeAt out.target.current.window.pointer.grant=some node ∧
      node.tag=out.target.current.node.tag ∧node.parent=out.target.current.node.parent ∧node.children=out.target.current.node.children ∧
      node.isExposed=out.target.current.node.isExposed) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin (CurrentCallCheckpointAsMutReturn.releasedTree seed)
      out.target.current.window.pointer.grant .Write out.target.current.physical.offset (out.target.current.physical.offset+1) := by
  obtain ⟨p,h,pMapped,hMapped,parents,owned,facets,active⟩:=released_same out done seed same
  have pEq : parent out=p:=by unfold parent;rw [pMapped];rfl
  have hEq : child out=h:=by unfold child;rw [hMapped];rfl
  have bankEq : bank out=extend (extend out.target.current.window.precise.completion p cp.source.grant) h p:=by
    dsimp only [bank];rw [ite_eq_left same,pEq,hEq]
  rw [bankEq]
  exact ⟨parents,owned,facets,active⟩

private theorem overwrite (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (first second : BorrowTree) :
    {{entry with allocation:=entry.allocation.setExtra first} with allocation:=
      ({entry with allocation:=entry.allocation.setExtra first} : LocalAllocation Provenance BorrowTree MiriMemoryKind).allocation.setExtra second}=
      {entry with allocation:=entry.allocation.setExtra second} := by
  cases entry with
  | mk kind allocation=>cases allocation;rfl

private theorem live_id {memory : MemoryState Provenance BorrowTree MiriMemoryKind} {oldId newId : AllocId}
    {entry : LocalAllocation Provenance BorrowTree MiriMemoryKind} (equal : oldId=newId)
    (present : memory.live.find? (fun row=>row.1==oldId)=some (oldId,entry)) :
    memory.live.find? (fun row=>row.1==newId)=some (newId,entry) := by
  cases equal
  exact present

variable (returned : CurrentCallCheckpointAsMutReturn.Returned seed)

def tree : BorrowTree:=if cp.output.id=cp.source.role.backing.id then CurrentCallCheckpointAsMutReturn.releasedTree seed
  else out.target.current.window.allocation.extra

/-- The selected Bool row in the actual post-pop machine, including the
untouched other-allocation branch. -/
theorem live : returned.machine.memory.live.find? (fun row=>row.1==out.target.current.id)=some
    (out.target.current.id,{out.target.current.physical.entry with allocation:=out.target.current.window.allocation.setExtra (tree out done seed)}) := by
  by_cases same : cp.output.id=cp.source.role.backing.id
  · have sourceId : out.target.current.id=out.source.role.backing.id:=out.target.id.trans (same.trans out.source.id.symm)
    have oldLive:=out.target.current.physical.live
    rw [out.target.current.physicalId,sourceId] at oldLive
    have sourceLive:=out.result.sourceLive
    rw [out.source.id] at oldLive
    have entryEq : out.target.current.physical.entry=CurrentCallCheckpointDefaultControl.entry out:=
      congrArg Prod.snd (Option.some.inj (oldLive.symm.trans sourceLive))
    have actual:=returned.sourceLive
    have parentEq : CurrentCallCheckpointAsMutControl.entry out=
        {out.target.current.physical.entry with allocation:=out.target.current.physical.entry.allocation.setExtra (CurrentCallCheckpointDefaultControl.tree out)} := by
      unfold CurrentCallCheckpointAsMutControl.entry
      rw [←entryEq]
    have installed := congrArg (fun entry : LocalAllocation Provenance BorrowTree MiriMemoryKind=>
      {entry with allocation:=entry.allocation.setExtra (CurrentCallCheckpointAsMutReturn.releasedTree seed)}) parentEq
    rw [overwrite] at installed
    have rowEq : {CurrentCallCheckpointAsMutControl.entry out with allocation:=
        (CurrentCallCheckpointAsMutControl.entry out).allocation.setExtra (CurrentCallCheckpointAsMutReturn.releasedTree seed)}=
        {out.target.current.physical.entry with allocation:=out.target.current.window.allocation.setExtra (tree out done seed)} := by
      dsimp only [tree]
      rw [ite_eq_left same]
      rw [out.target.current.physicalAllocation] at installed
      exact installed
    rw [rowEq] at actual
    exact live_id sourceId.symm actual
  · have different : out.target.current.id≠out.source.role.backing.id:=by
      intro equal;apply same;exact out.target.id.symm.trans (equal.trans out.source.id)
    have oldLive:=out.target.current.physical.live
    rw [out.target.current.physicalId] at oldLive
    have beforeLive : (CurrentCallCheckpointDefaultControl.machine out).memory.live.find? (fun row=>row.1==out.target.current.id)=some
        (out.target.current.id,out.target.current.physical.entry) := by
      change (RetagEntry.updatedMemory out.machine.memory out.source.role.backing.id (CurrentCallCheckpointDefaultControl.entry out)
        (CurrentCallCheckpointDefaultControl.tree out)).live.find? _=_
      exact StackPopRelease.lookup_commit_other out.machine.memory out.source.role.backing.id out.target.current.id
        (CurrentCallCheckpointDefaultControl.entry out) out.target.current.physical.entry (CurrentCallCheckpointDefaultControl.tree out) different oldLive
    rw [returned.memory]
    have actual:=StackPopRelease.lookup_commit_other (CurrentCallCheckpointDefaultControl.machine out).memory out.source.role.backing.id out.target.current.id
      (CurrentCallCheckpointAsMutControl.entry out) out.target.current.physical.entry (CurrentCallCheckpointAsMutReturn.releasedTree seed) different beforeLive
    have self : out.target.current.window.allocation.setExtra out.target.current.window.allocation.extra=out.target.current.window.allocation:=by
      cases out.target.current.window.allocation;rfl
    dsimp only [tree]
    rw [ite_eq_right same,self,←out.target.current.physicalAllocation]
    exact actual


structure Packet where
  current : Return returned.machine (CurrentCallCheckpointAsMutReturn.postTracker seed) place
  id : current.id=cp.output.id
  offset : current.offset=cp.output.offset
  pointer : current.window.pointer=out.target.current.window.pointer
  original : current.original=out.target.current.original
  allocated : current.window.allocation=out.target.current.window.allocation.setExtra (tree out done seed)
  completion : current.window.precise.completion=bank out
  tag : current.node.tag=out.target.current.node.tag
  parent : current.node.parent=out.target.current.node.parent

/-- The actual common AsMut return retains the one-byte Bool window and the
ORIGINAL destination licence, for both shared and different allocation IDs. -/
theorem invoke : Nonempty (Packet out done seed returned) := by
  have rootTag : (CurrentCallCheckpointAsMutReturn.postTracker seed).global.rootTag? out.target.current.id=
      (CurrentCallCheckpointLenControl.postTracker cp).global.rootTag? out.target.current.id := by
    change (seed.output.global.endCall seed.output.frame).rootTag? _=_
    rw [CurrentCallCheckpointAsMutControl.helper_output out done seed]
    rfl
  have addresses:=CurrentCallCheckpointAsMutFacts.addresses out done seed returned
  have extras:=CurrentCallCheckpointAsMutFacts.extras out done seed returned
  have actualLive:=live out done seed returned
  by_cases same : cp.output.id=cp.source.role.backing.id
  · have treeEq : tree out done seed=CurrentCallCheckpointAsMutReturn.releasedTree seed:=by dsimp only [tree];rw [ite_eq_left same]
    obtain ⟨parents,owned,⟨node,nodeAt,nodeTag,nodeParent,nodeChildren,nodeHidden⟩,active⟩:=same_raw out done seed same
    obtain ⟨metadata,capacity,roots,short⟩:=metadata_same out done seed same
    rw [treeEq] at actualLive
    obtain ⟨current,id,offset,pointer,original,allocated,completed,tag,parent⟩:=CurrentCallCheckpointBoolInstall.install
      out.target.current returned.machine (CurrentCallCheckpointAsMutReturn.postTracker seed) (CurrentCallCheckpointAsMutReturn.releasedTree seed)
      (bank out) actualLive addresses extras rootTag (runtime out done seed) parents capacity roots metadata (edges_same out same)
      owned (by rw [roots];exact out.target.current.distinct) short node nodeAt nodeTag nodeParent
      (nodeChildren.trans out.target.current.leaf) (nodeHidden.trans out.target.current.hidden) active
    refine ⟨{
      current:=current,id:=id.trans out.target.id,offset:=offset.trans out.target.offset,pointer:=pointer,original:=original
      allocated:=?_,completion:=completed,tag:=tag,parent:=parent}⟩
    rw [treeEq]
    exact allocated
  · have treeEq : tree out done seed=out.target.current.window.allocation.extra:=by dsimp only [tree];rw [ite_eq_right same]
    have bankEq : bank out=out.target.current.window.precise.completion:=by dsimp only [bank];rw [ite_eq_right same]
    have flags : (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags=
        (CurrentCallCheckpointLenControl.postTracker cp).global.protectedTags := by
      change (seed.output.global.endCall seed.output.frame).protectedTags=_
      rw [CurrentCallCheckpointAsMutControl.helper_output out done seed]
      exact CurrentCallCheckpointAcceptedBoolFrame.final_flags cp out.result out.source
    have currentRuntime:=CurrentCallCheckpointAcceptedBoolFrame.different_runtime cp out.result out.source out.target
    have exactRuntime : DuplicatePrefixBorrowContract.RuntimeFacts out.target.current.window.allocation.extra
        (CurrentCallCheckpointAsMutReturn.postTracker seed).global := by
      change DuplicatePrefixBorrowContract.RuntimeFacts _ (seed.output.global.endCall seed.output.frame)
      rw [CurrentCallCheckpointAsMutControl.helper_output out done seed]
      exact currentRuntime
    have endEq : (out.target.current.physical.offset+1).toNat=out.target.current.offset+1 := by
      rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt,out.target.current.physicalOffset]
      exact Nat.lt_of_le_of_lt out.target.current.physical.bounds out.target.current.physical.capacity.toNat_lt
    have owned:=(checkpoint_bool_rule "CurrentCallExclusiveWindowFrame.window_owned") out.target.current.window rfl out.target.current.runtime
      out.target.current.physical.offset (out.target.current.physical.offset+1)
      (by have equal:=out.target.current.physicalOffset;omega) (by rw [endEq];exact Nat.le_refl _)
    have exactOwned : OwnedOn (Authority out.target.current.window.allocation.extra out.target.current.window.precise.completion
        (CurrentCallCheckpointAsMutReturn.postTracker seed).global.protectedTags out.target.current.window.pointer.grant)
        out.target.current.physical.offset (out.target.current.physical.offset+1) out.target.current.window.allocation.extra.locations := by rw [flags];exact owned
    rw [treeEq] at actualLive
    obtain ⟨current,id,offset,pointer,original,allocated,completed,tag,parent⟩:=CurrentCallCheckpointBoolInstall.install
      out.target.current returned.machine (CurrentCallCheckpointAsMutReturn.postTracker seed) out.target.current.window.allocation.extra
      out.target.current.window.precise.completion actualLive addresses extras rootTag exactRuntime out.target.current.window.parents rfl rfl
      (by intro query previous found;exact ⟨previous,found,rfl,rfl,rfl,rfl⟩) (by intro query origin edge;exact edge) exactOwned
      out.target.current.distinct out.target.current.short out.target.current.node out.target.current.nodeAt rfl rfl
      out.target.current.leaf out.target.current.hidden out.target.current.activity
    refine ⟨{
      current:=current,id:=id.trans out.target.id,offset:=offset.trans out.target.offset,pointer:=pointer,original:=original
      allocated:=?_,completion:=?_,tag:=tag,parent:=parent}⟩
    · rw [treeEq];exact allocated
    · rw [bankEq];exact completed

end
end DuplicatePrefix.CurrentCallCheckpointAcceptedBoolCurrent
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointAcceptedBoolCurrent" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved accepted Bool current dependency {dependency}"
