import duplicate_prefix.CurrentCallCheckpointMutableCurrent
import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
import duplicate_prefix.GeneralBorrowRawTargetActivity
import duplicate_prefix.GeneralBorrowSharedFnEntryGlobalReturn
namespace DuplicatePrefix.CurrentCallCheckpointMutableParents
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open S05ConcreteProtectedChildCompletion S05CompletedAncestryReadMutable
open CurrentCallPostEntryCheckpoint CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
open CurrentCallCheckpointMutable
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
noncomputable section
variable {options remaining span len count place limits} (cp : Checkpoint options remaining span len count place)
  (control : CurrentCallCheckpointLenReturn.Result cp limits) (source : CurrentCallCheckpointLenSource.Data cp control)

theorem p_frame : ∃pIndex pNode qNode,
    (tree cp control source).indexOfTag (tracker cp).global.nextPointerTag=some pIndex ∧
    (tree cp control source).nodes.get pIndex=some pNode ∧pNode.tag=(tracker cp).global.nextPointerTag ∧pNode.parent=some cp.source.grant ∧
    (tree cp control source).nodes.get cp.source.grant=some qNode ∧qNode.tag=cp.source.tag ∧qNode.isExposed=false ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin (tree cp control source) cp.source.grant .Write (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len) := by
  have positive:=cp.source.positive
  have nonzero : len≠0:=by intro zero;rw [zero] at positive;cases positive
  have short : source.role.backing.allocation.extra.nodes.size<65536:=by have budget:=source.nodes;omega
  have nodeRoom : source.role.backing.allocation.extra.nodes.size+1≤4294967295:=by omega
  obtain ⟨oldParent,node,oldMapped,oldAt,nodeTag,readDone,childDone,afterRuntime,capacity,growth,newChild,newLookup,both,active⟩:=
    CurrentCallSpatialDefaultMutable.construct source.role source.runtime source.distinct short nodeRoom cp.source.tag source.concrete
      (room cp control source) (UInt64.ofNat cp.offset) len (CurrentCallCheckpointShared.start_eq cp) rfl nonzero (bounds cp control source)
  obtain ⟨readParent,readNode,readMapped,readAt,readTag,_,readRuntime,nodes,roots,tags,readCapacity,normal,parents⟩:=
    CurrentCallSpatialDefaultShared.prepare source.role source.runtime source.distinct short cp.source.tag source.concrete (room cp control source)
      (UInt64.ofNat cp.offset) len (CurrentCallCheckpointShared.start_eq cp) rfl nonzero (bounds cp control source)
  have sameParent : readParent=oldParent:=Option.some.inj (readMapped.symm.trans oldMapped)
  subst readParent
  have sameNode : readNode=node:=Option.some.inj (readAt.symm.trans oldAt)
  subst readNode
  let accessed:=CurrentCallSpatialDefaultShared.accessed source.role cp.source.tag (UInt64.ofNat cp.offset) len
  have high:=GeneralBorrowForestTagHighWater.complete source.role.backing.allocation.extra _ _ source.runtime.below source.runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩:=GenericFunctionTagFormation.fresh_above source.role.backing.allocation.extra _ _ (tracker cp).global.nextPointerTag high (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping (tracker cp).global.nextPointerTag:=by rw [tags];exact fresh
  have parentAt : accessed.tree.nodeAt oldParent=some node:=by change accessed.tree.nodes.get _=_;rw [nodes];exact oldAt
  have parentTagged : accessed.tree.indexOfTag cp.source.tag=some oldParent:=by change accessed.tree.tagMapping.get _=_;rw [tags];exact oldMapped
  have roomAfter : accessed.tree.nodes.size+1≤4294967295:=by rw [nodes];exact nodeRoom
  have boundsAfter : (UInt64.ofNat cp.offset).toNat+len.toNat≤accessed.tree.locations.size.bytes.toNat:=by rw [readCapacity];exact bounds cp control source
  have tagBound : (tracker cp).global.nextPointerTag.value.toNat<(next cp control source).global.nextPointerTag.value.toNat:=by
    have successor:=GenericFunctionEntryNumerics.successor_value (tracker cp).global.nextPointerTag (room cp control source)
    change (tracker cp).global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag (tracker cp).global.nextPointerTag (room cp control source)).value.toNat
    omega
  obtain ⟨i,cell⟩:=source.role.covered (source.role.backing.id,cp.offset) ⟨rfl,Nat.le_refl _,by omega⟩
  let overlap : CurrentCallSpatialSourceCover.Active source.role i:=⟨_,⟨rfl,Nat.le_refl _,by omega⟩,cell⟩
  have primary : ∃rootNode,accessed.tree.nodes.get allocationRoot=some rootNode:=by
    obtain ⟨rootNode,atRoot,_⟩:=(source.role.roles i overlap).issued.capability.rootNode
    exact ⟨rootNode,by rw [nodes];exact atRoot⟩
  have parentOrder : node.tag.value≤(tracker cp).global.nextPointerTag.value:=
    UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp (GeneralBorrowParentTagInvariant.parent_below_fresh _ _ source.runtime oldParent node oldAt)))
  obtain ⟨_,_,_,_,pChild,pLookup,leaf,_,_,_⟩:=(spatial_install_rule ".CurrentCallResourceDefaultMutable.completion_construct") accessed.tree
    (next cp control source).global source.role.backing.cells[i].completion readRuntime (parents i) cp.source.tag (tracker cp).global.nextPointerTag
    oldParent node parentTagged parentAt freshAfter roomAfter tagBound unheld (UInt64.ofNat cp.offset) len nonzero boundsAfter primary parentOrder
  have qMapped : source.role.backing.allocation.extra.indexOfTag cp.source.tag=some cp.source.grant:=by
    have mapped:=source.runtime.formed.allocator.nodeTags _ _ source.nodeAt
    rw [source.nodeTag] at mapped
    exact mapped
  have sameParent : oldParent=cp.source.grant:=Option.some.inj (oldMapped.symm.trans qMapped)
  subst oldParent
  have sameOld : node=source.node:=Option.some.inj (oldAt.symm.trans source.nodeAt)
  subst node
  obtain ⟨qNode,qAt,qTag,_,qHidden⟩:=leaf.old cp.source.grant source.node parentAt
  obtain ⟨other,otherLookup,⟨pNode,pAt,pTag,pHidden⟩,_⟩:=GeneralBorrowDefaultChildMetadata.construct accessed.tree _ readRuntime cp.source.tag (tracker cp).global.nextPointerTag cp.source.grant source.node parentTagged parentAt freshAfter roomAfter (UInt64.ofNat cp.offset) len nonzero boundsAfter
  have sameChild : other=pChild:=Option.some.inj (otherLookup.symm.trans pLookup)
  subst other
  obtain ⟨physicalNode,physicalAt,physicalParent⟩:=leaf.childLive
  have sameNode : pNode=physicalNode:=Option.some.inj (pAt.symm.trans physicalAt)
  have pParent : pNode.parent=some cp.source.grant:=sameNode ▸ physicalParent
  have readActivity : GeneralBorrowFreshActiveWithin.ActiveWithin accessed.tree cp.source.grant .Write (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len):=by
    exact GeneralBorrowFreshActiveWithinAccess.normal source.role.backing.allocation.extra cp.source.tag (Size.ofBytes (UInt64.ofNat cp.offset)) (Size.ofBytes len) .Read
      (tracker cp).global.protectedTags .VisitChildrenOfAccessed cp.source.grant (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len)
      source.runtime.formed.well (bounds cp control source) (Nat.le_refl _) (Nat.le_refl _) source.activity
  have activity:=GeneralBorrowRawTargetActivity.default_child accessed.tree _ readRuntime cp.source.tag (tracker cp).global.nextPointerTag cp.source.grant source.node parentTagged parentAt freshAfter roomAfter
    (UInt64.ofNat cp.offset) len nonzero boundsAfter cp.source.grant (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len) (Nat.le_refl _) (Nat.le_refl _) readActivity
  refine ⟨pChild,pNode,qNode,pLookup,pAt,pTag,pParent,qAt,?_,?_,activity⟩
  · exact qTag.trans source.nodeTag
  · exact qHidden.trans source.hidden
theorem s_frame : ∃pIndex sIndex pNode qNode sNode,
    (sOutput cp control source).child.tree.indexOfTag (sOutput cp control source).tag=some sIndex ∧
    (sOutput cp control source).child.tree.nodes.get sIndex=some sNode ∧sNode.tag=(sOutput cp control source).tag ∧sNode.parent=some pIndex ∧
    (sOutput cp control source).child.tree.nodes.get pIndex=some pNode ∧pNode.tag=(tracker cp).global.nextPointerTag ∧pNode.parent=some cp.source.grant ∧
    (sOutput cp control source).child.tree.nodes.get cp.source.grant=some qNode ∧qNode.tag=cp.source.tag ∧qNode.isExposed=false ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin (sOutput cp control source).child.tree cp.source.grant .Write (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len) := by
  let p:=prepared cp control source
  let role:=p.role
  let accessed:=CurrentCallSpatialEntryRead.read role {} p.room (UInt64.ofNat cp.offset) len
  have nonzero : len≠0:=by intro zero;have positive:=cp.source.positive;rw [zero] at positive;cases positive
  obtain ⟨contract,afterRuntime,_⟩:=CurrentCallSpatialEntryRead.invoke role rfl p.runtime p.distinct p.short {} p.room (UInt64.ofNat cp.offset) len (CurrentCallCheckpointShared.start_eq cp) rfl nonzero p.bounds
  have positive:=cp.source.positive
  obtain ⟨i,cell⟩:=role.covered (role.backing.id,cp.offset) ⟨rfl,Nat.le_refl _,by omega⟩
  let overlap : CurrentCallSpatialSourceCover.Active role i:=⟨_,⟨rfl,Nat.le_refl _,by omega⟩,cell⟩
  obtain ⟨parent,parentAt,mapped,binding⟩:=(role.roles i overlap).binding
  have provenance : role.family.value.provenance=.concrete source.role.backing.id (tracker cp).global.nextPointerTag:=p_provenance cp control source
  change (match role.family.value.provenance with | .concrete id tag=>id=role.family.allocation ∧tag=parent.tag | .wildcard=>parent.isExposed=true) at binding
  rw [provenance] at binding
  have parentAt' : accessed.tree.nodes.get (role.roles i overlap).grant=some parent:=by rw [contract.nodes];exact parentAt
  have tagged : accessed.tree.indexOfTag parent.tag=some (role.roles i overlap).grant:=afterRuntime.formed.allocator.nodeTags _ _ parentAt'
  obtain ⟨_,held,_,_,_,fresh⟩:=GeneralBorrowFnEntryRegistrationRuntime.prepare role.backing.allocation.extra (next cp control source).global {} role.backing.id p.room p.runtime
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping (next cp control source).global.nextPointerTag:=by rw [contract.tags];exact fresh
  have roomAfter : accessed.tree.nodes.size+1≤4294967295:=by change accessed.tree.nodes.data.size+1≤_;rw [contract.nodes];exact p.nodeRoom
  have boundsAfter : (UInt64.ofNat cp.offset).toNat+len.toNat≤accessed.tree.locations.size.bytes.toNat:=by rw [contract.capacity];exact p.bounds
  have boundTag : (next cp control source).global.nextPointerTag.value.toNat<(CurrentCallSpatialEntryRead.registeredTracker role {} p.room).global.nextPointerTag.value.toNat:=by
    have successor:=GenericFunctionEntryNumerics.successor_value (next cp control source).global.nextPointerTag p.room
    change (next cp control source).global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag (next cp control source).global.nextPointerTag p.room).value.toNat
    omega
  have heldTag : (CurrentCallSpatialEntryRead.registeredTracker role {} p.room).global.protectedTags.contains (next cp control source).global.nextPointerTag=true:=by
    unfold ProtectedTags.contains
    change ((GeneralBorrowFnEntryRegistration.registered (next cp control source).global {} role.backing.id p.room).1.protectedTags.get (next cp control source).global.nextPointerTag).isSome=true
    rw [held];rfl
  obtain ⟨_,_,_,_,child,lookup,leaf,_⟩:=CurrentCallParentInsertion.concrete_frame accessed.tree _ afterRuntime parent.tag (next cp control source).global.nextPointerTag (role.roles i overlap).grant parent tagged parentAt' freshAfter roomAfter boundTag heldTag (UInt64.ofNat cp.offset) len nonzero boundsAfter
  obtain ⟨other,otherLookup,active⟩:=GeneralBorrowConstructorChildActivity.Protected.construct accessed.tree _ afterRuntime parent.tag (next cp control source).global.nextPointerTag (role.roles i overlap).grant parent tagged parentAt' freshAfter roomAfter (UInt64.ofNat cp.offset) len nonzero boundsAfter
  have same : other=child:=Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  obtain ⟨other,otherLookup,⟨node,nodeAt,nodeTag,hidden⟩,_⟩:=GeneralBorrowProtectedChildMetadata.construct accessed.tree _ afterRuntime parent.tag (next cp control source).global.nextPointerTag (role.roles i overlap).grant parent tagged parentAt' freshAfter roomAfter (UInt64.ofNat cp.offset) len nonzero boundsAfter
  have same : other=child:=Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  obtain ⟨pIndex,oldP,oldQ,pLookup,pAt,pTag,pParent,qAt,qTag,qHidden,qActivity⟩:=p_frame cp control source
  have beforeP : role.backing.allocation.extra.nodes.get pIndex=some oldP:=by rw [p_tree cp control source];exact pAt
  have beforeQ : role.backing.allocation.extra.nodes.get cp.source.grant=some oldQ:=by rw [p_tree cp control source];exact qAt
  have pMapped : role.backing.allocation.extra.indexOfTag (tracker cp).global.nextPointerTag=some pIndex:=by rw [p_tree cp control source];exact pLookup
  have concreteRole : role.family.value.provenance=.concrete role.backing.id (tracker cp).global.nextPointerTag:=by
    rw [p_provenance cp control source,p.id]
  have grantEq : (role.roles i overlap).grant=pIndex:=CurrentCallSpatialSharedCover.grant_eq role concreteRole pMapped i overlap
  obtain ⟨physical,physicalAt,physicalParent⟩:=leaf.childLive
  have sameNode : node=physical:=Option.some.inj (nodeAt.symm.trans physicalAt)
  have sParent : node.parent=some pIndex:=by rw [sameNode,physicalParent,grantEq]
  have allOld:=(s_operation cp control source).2.2.2.2.2.2
  obtain ⟨actualChild,actualLookup,oldRoots,oldFields,actualNode⟩:=allOld
  obtain ⟨newP,newPAt,newPTag,newPParent,_,_⟩:=oldFields pIndex oldP beforeP
  obtain ⟨newQ,newQAt,newQTag,_,newQHidden,_⟩:=oldFields cp.source.grant oldQ beforeQ
  have actualEq : (sOutput cp control source).child.tree=
      (accessed.tree.newChild (Size.ofBytes (UInt64.ofNat cp.offset)) (.concrete parent.tag)
        (next cp control source).global.nextPointerTag (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree:=by
    change (accessed.tree.newChild _ (match role.family.value.provenance with | .concrete _ tag=>.concrete tag | .wildcard=>.wildcard) _ _ _ _).tree=_
    rw [provenance]
    dsimp only
    rw [binding.2]
  have beforeActivity : GeneralBorrowFreshActiveWithin.ActiveWithin role.backing.allocation.extra cp.source.grant .Write (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len):=by rw [p_tree cp control source];exact qActivity
  have readActivity : GeneralBorrowFreshActiveWithin.ActiveWithin accessed.tree cp.source.grant .Write (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len):=by
    have normal:=GeneralBorrowFreshActiveWithinAccess.normal role.backing.allocation.extra (tracker cp).global.nextPointerTag (Size.ofBytes (UInt64.ofNat cp.offset)) (Size.ofBytes len) .Read
      (CurrentCallSpatialEntryRead.registeredTracker role {} p.room).global.protectedTags .VisitChildrenOfAccessed cp.source.grant (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len)
      p.runtime.formed.well p.bounds (Nat.le_refl _) (Nat.le_refl _) beforeActivity
    simpa only [accessed,CurrentCallSpatialEntryRead.read,CurrentCallSpatialRows.provenance,provenance,BorrowTree.performNormalAccessRange] using normal
  have finalActivity:=GeneralBorrowRawTargetActivity.protected_child accessed.tree _ afterRuntime parent.tag (next cp control source).global.nextPointerTag (role.roles i overlap).grant parent tagged parentAt' freshAfter roomAfter
    (UInt64.ofNat cp.offset) len nonzero boundsAfter cp.source.grant (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len) (Nat.le_refl _) (Nat.le_refl _) readActivity
  refine ⟨pIndex,child,newP,newQ,node,?_,?_,nodeTag,sParent,newPAt,newPTag.trans pTag,newPParent.trans pParent,newQAt,newQTag.trans qTag,newQHidden.trans qHidden,?_⟩
  · rw [actualEq];exact lookup
  · rw [actualEq];exact nodeAt
  · rw [actualEq];exact finalActivity

theorem final_flags : ((sOutput cp control source).global.endCall (sOutput cp control source).frame).protectedTags=(tracker cp).global.protectedTags := by
  let p:=prepared cp control source
  have exactGlobal:=GeneralBorrowSharedFnEntryGlobalReturn.global p.role.backing.allocation.extra (next cp control source).global p.runtime {} p.role.backing.id p.room
  change ((GeneralBorrowFnEntryRegistration.registered (next cp control source).global {} p.role.backing.id p.room).1.endCall
    (({} : FrameState).addProtector p.role.backing.id (next cp control source).global.nextPointerTag)).protectedTags=_
  rw [exactGlobal]
  rfl

theorem parent_unheld : ((sOutput cp control source).global.endCall (sOutput cp control source).frame).protectedTags.contains (tracker cp).global.nextPointerTag=false := by
  rw [final_flags cp control source]
  have high:=GeneralBorrowForestTagHighWater.complete source.role.backing.allocation.extra _ _ source.runtime.below source.runtime.formed.allocator.nodeTags
  exact (GenericFunctionTagFormation.fresh_above source.role.backing.allocation.extra _ _ (tracker cp).global.nextPointerTag high (Nat.le_refl _)).2.2

theorem child_unheld : ((sOutput cp control source).global.endCall (sOutput cp control source).frame).protectedTags.contains (sOutput cp control source).tag=false := by
  rw [StackPopRelease.end_call_contains]
  have member : (sOutput cp control source).tag∈(sOutput cp control source).frame.protectedTags.toList.map Prod.snd:=by
    change (next cp control source).global.nextPointerTag∈[(next cp control source).global.nextPointerTag]
    simp only [List.mem_singleton]
  simp only [member,ite_true]

end
end DuplicatePrefix.CurrentCallCheckpointMutableParents
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointMutableParents" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved mutable parents dependency {dependency}"
