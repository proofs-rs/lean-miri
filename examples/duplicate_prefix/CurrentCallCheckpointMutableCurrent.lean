import duplicate_prefix.CurrentCallCheckpointMutable
import duplicate_prefix.CurrentCallSpatialSourceInstall
import duplicate_prefix.GeneralBorrowConstructorChildActivity
import duplicate_prefix.GeneralBorrowProtectedChildMetadata
import duplicate_prefix.CurrentCallSpatialProtectorRelease

namespace DuplicatePrefix.CurrentCallCheckpointMutableCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallPostEntryCheckpoint CurrentCallResourceNormalization CurrentCallSpatialCover GeneralRangeMapOrigins
open CurrentCallCheckpointMutable
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section
variable {options remaining span len count place limits} (cp : Checkpoint options remaining span len count place)
  (control : CurrentCallCheckpointLenReturn.Result cp limits) (source : CurrentCallCheckpointLenSource.Data cp control)

/-- The actual helper installation supplies presence; all child resources are
then derived from the same S operation and its fixed current P cover. -/
theorem resources (post : Before) (nextTracker : MachineHooks.BorrowState)
    (present : Present (ActualWorld post) (prepared cp control source).role.backing.id
      ((prepared cp control source).role.backing.allocation.setExtra (sOutput cp control source).child.tree))
    (rootTag : nextTracker.global.rootTag? (prepared cp control source).role.backing.id=
      (next cp control source).global.rootTag? (prepared cp control source).role.backing.id)
    (flags : nextTracker.global.protectedTags=(sOutput cp control source).global.protectedTags) :
    ∃child,(sOutput cp control source).child.tree.indexOfTag (sOutput cp control source).tag=some child ∧
      CurrentCallSpatialSourceInstall.CellResources (prepared cp control source).role post nextTracker
        (sOutput cp control source).child.tree (sOutput cp control source).tag child := by
  have nonzero : len≠0:=by intro zero;have positive:=cp.source.positive;rw [zero] at positive;cases positive
  exact CurrentCallSpatialSourceInstall.resources (prepared cp control source).role rfl
    (prepared cp control source).runtime (prepared cp control source).distinct (prepared cp control source).short
    (prepared cp control source).nodeRoom {} (prepared cp control source).room (UInt64.ofNat cp.offset) len
    (CurrentCallCheckpointShared.start_eq cp) rfl nonzero (prepared cp control source).bounds post nextTracker present rootTag flags

/-- Source-only cover on the actual helper world. No unchanged pre-world is
used for the installed S tree. -/
theorem cover (post : Before) (nextTracker : MachineHooks.BorrowState)
    (present : Present (ActualWorld post) (prepared cp control source).role.backing.id
      ((prepared cp control source).role.backing.allocation.setExtra (sOutput cp control source).child.tree))
    (rootTag : nextTracker.global.rootTag? (prepared cp control source).role.backing.id=
      (next cp control source).global.rootTag? (prepared cp control source).role.backing.id)
    (flags : nextTracker.global.protectedTags=(sOutput cp control source).global.protectedTags) :
    ∃context : CurrentCallSpatialCover.Context post, ∃role : RoleCover post nextTracker context .mut cp.offset len.toNat,
      role.backing.allocation=(prepared cp control source).role.backing.allocation.setExtra (sOutput cp control source).child.tree ∧
      role.backing.id=(prepared cp control source).role.backing.id ∧
      role.family=CurrentCallSpatialSourceInstall.childFamily (prepared cp control source).role (sOutput cp control source).tag := by
  obtain ⟨child,lookup,owned⟩:=resources cp control source post nextTracker present rootTag flags
  let updates:=CurrentCallSpatialSourceInstall.updates (prepared cp control source).role rfl owned
  let context:=CurrentCallSpatialSourceCover.context (prepared cp control source).role present updates
  let role:=CurrentCallSpatialSourceInstall.sourceCover (prepared cp control source).role rfl present owned
  exact ⟨context,role,rfl,rfl,rfl⟩

/-- Physical S metadata and activity come from the one actual constructor,
independently of all logical completion choices. -/
theorem facets :
    ∃child node,(sOutput cp control source).child.tree.indexOfTag (sOutput cp control source).tag=some child ∧
      (sOutput cp control source).child.tree.nodes.get child=some node ∧node.tag=(sOutput cp control source).tag ∧
      node.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (sOutput cp control source).child.tree child .Write (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len) ∧
      (sOutput cp control source).child.tree.roots=(prepared cp control source).role.backing.allocation.extra.roots := by
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
  have roots:=leaf.roots.trans contract.roots
  have actualEq : (sOutput cp control source).child.tree=
      (accessed.tree.newChild (Size.ofBytes (UInt64.ofNat cp.offset)) (.concrete parent.tag)
        (next cp control source).global.nextPointerTag (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree:=by
    change (accessed.tree.newChild _ (match role.family.value.provenance with | .concrete _ tag=>.concrete tag | .wildcard=>.wildcard) _ _ _ _).tree=_
    rw [provenance]
    dsimp only
    rw [binding.2]
  refine ⟨child,node,?_,?_,nodeTag,hidden,?_,?_⟩
  · rw [actualEq];exact lookup
  · rw [actualEq];exact nodeAt
  · rw [actualEq];exact active
  · rw [actualEq];exact roots

theorem short : (sOutput cp control source).child.tree.nodes.size<65536 := by
  have positive:=cp.source.positive
  have nonzero : len≠0:=by intro zero;rw [zero] at positive;cases positive
  have oldShort : source.role.backing.allocation.extra.nodes.size<65536:=by have budget:=source.nodes;omega
  have nodeRoom : source.role.backing.allocation.extra.nodes.size+1≤4294967295:=by omega
  obtain ⟨_,_,_,_,_,_,_,_,_,growth,_⟩:=CurrentCallSpatialDefaultMutable.construct source.role source.runtime source.distinct oldShort nodeRoom cp.source.tag source.concrete
    (room cp control source) (UInt64.ofNat cp.offset) len (CurrentCallCheckpointShared.start_eq cp) rfl nonzero (bounds cp control source)
  have pGrowth : (prepared cp control source).role.backing.allocation.extra.nodes.size≤source.role.backing.allocation.extra.nodes.size+1:=by
    rw [p_tree cp control source];exact growth
  have sGrowth : (sOutput cp control source).child.tree.nodes.size≤(prepared cp control source).role.backing.allocation.extra.nodes.size+1 := (s_operation cp control source).2.2.2.2.2.1
  have budget:=source.nodes
  omega

/-- One actual S release uses the installed all-cell bank. Presence is the
literal helper installation certificate, never an original admission gate. -/
theorem release (post : Before)
    (present : Present (ActualWorld post) (prepared cp control source).role.backing.id
      ((prepared cp control source).role.backing.allocation.setExtra (sOutput cp control source).child.tree)) :
    let output:=sOutput cp control source
    (output.child.tree.releaseProtector output.tag output.global.protectedTags).status=.Released ∧
      DuplicatePrefixBorrowContract.RuntimeFacts (output.child.tree.releaseProtector output.tag output.global.protectedTags).tree output.global ∧
      (output.child.tree.releaseProtector output.tag output.global.protectedTags).tree=
        {output.child.tree with locations:=(output.child.tree.releaseProtector output.tag output.global.protectedTags).tree.locations} ∧
      (output.child.tree.releaseProtector output.tag output.global.protectedTags).tree.locations.size=output.child.tree.locations.size := by
  let nextTracker : MachineHooks.BorrowState:=⟨(sOutput cp control source).global,(next cp control source).retagMode⟩
  have rootTag : nextTracker.global.rootTag? (prepared cp control source).role.backing.id=(next cp control source).global.rootTag? (prepared cp control source).role.backing.id:=rfl
  obtain ⟨context,Q,allocation,idEq,family⟩:=cover cp control source post nextTracker present rootTag rfl
  have treeEq : Q.backing.allocation.extra=(sOutput cp control source).child.tree:=by
    rw [allocation];rfl
  obtain ⟨child,node,lookup,nodeAt,tag,hidden,active,roots⟩:=facets cp control source
  have currentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts Q.backing.allocation.extra nextTracker.global:=by
    rw [treeEq];exact (s_operation cp control source).2.2.2.1
  have distinct : Q.backing.allocation.extra.roots.toList.Nodup:=by rw [treeEq,roots];exact (prepared cp control source).distinct
  have currentShort : Q.backing.allocation.extra.nodes.size<65536:=by rw [treeEq];exact short cp control source
  have currentAt : Q.backing.allocation.extra.nodes.get child=some node:=by rw [treeEq];exact nodeAt
  have concrete : Q.family.value.provenance=.concrete Q.backing.id node.tag:=by
    rw [family,idEq]
    change Provenance.concrete (prepared cp control source).role.backing.id (sOutput cp control source).tag=_
    rw [tag]
  have currentActive : GeneralBorrowFreshActiveWithin.ActiveWithin Q.backing.allocation.extra child .Write (UInt64.ofNat cp.offset) ((UInt64.ofNat cp.offset)+len):=by rw [treeEq];exact active
  have noWrap : ((UInt64.ofNat cp.offset)+len).toNat=(UInt64.ofNat cp.offset).toNat+len.toNat:=by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt (prepared cp control source).bounds (UInt64.toNat_lt (prepared cp control source).role.backing.allocation.extra.locations.size.bytes)
  have positive : (UInt64.ofNat cp.offset).toNat<((UInt64.ofNat cp.offset)+len).toNat:=by rw [noWrap];have positive:=cp.source.positive;omega
  obtain ⟨done,shape,runtime,capacity,_⟩:=CurrentCallSpatialProtectorRelease.release Q rfl currentRuntime distinct currentShort child node currentAt concrete hidden
    (UInt64.ofNat cp.offset) len (CurrentCallCheckpointShared.start_eq cp) rfl positive noWrap currentActive
  rw [treeEq,tag] at done shape runtime capacity
  exact ⟨done,runtime,shape,capacity⟩

end
end DuplicatePrefix.CurrentCallCheckpointMutableCurrent
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointMutableCurrent" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved mutable-current dependency {dependency}"
