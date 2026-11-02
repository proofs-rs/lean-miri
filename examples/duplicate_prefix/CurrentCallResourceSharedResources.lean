import duplicate_prefix.CurrentCallResourceSharedStage
import duplicate_prefix.CurrentCallSharedReadResources
import duplicate_prefix.CurrentCallResourceBoolFacets

namespace DuplicatePrefix.CurrentCallResourceSharedResources
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open GeneralBorrowFnEntryRegistration GeneralRangeMapOrigins GeneralBorrowRawSharedExpression
open CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

structure Stage {before tracker data owner id offset length}
    (Q : UniformWindow before tracker data owner id offset length .mut)
    (tag : BorTag) (start amount : UInt64)
    (room : tracker.global.nextPointerTag.value<18446744073709551615) where
  preparation : CurrentCallResourceDefaultShared.Preparation Q tag start amount room
  done : (child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).outcome=.ok ()
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts
    (child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree (advanced tracker.global room)
  capacity : (child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.locations.size=Q.allocation.extra.locations.size
  growth : (child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.nodes.size≤Q.allocation.extra.nodes.size+1
  reader : UniIndex
  lookup : (child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.indexOfTag tracker.global.nextPointerTag=some reader
  parents : ParentInterpretation (child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree
    (S05ConcreteProtectedChildCompletion.extend Q.precise.completion reader Q.pointer.grant)
  capabilities : OwnedOn (GeneralBorrowSharedReadConstructor.Capabilities
    (child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree
    tracker.global.protectedTags Q.pointer.grant reader) start (start+amount)
    (child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.locations
  activity : GeneralBorrowFreshActiveWithin.ActiveWithin
    (child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree reader .Read start (start+amount)
  rows : OwnedOn (S05CurrentReadProtectorRelease.Authority
    (child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree
    (S05ConcreteProtectedChildCompletion.extend Q.precise.completion reader Q.pointer.grant)
    tracker.global.protectedTags preparation.geometry.selectedRoot Q.pointer.grant reader) start (start+amount)
    (child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.locations

private theorem parents {before tracker data owner id offset length}
    (Q : UniformWindow before tracker data owner id offset length .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra tracker.global)
    (tag : BorTag) (concrete : Q.pointer.value.provenance=.concrete id tag)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (P : CurrentCallResourceDefaultShared.Preparation Q tag start amount room)
    (nodeRoom : Q.allocation.extra.nodes.size+1≤4294967295) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤Q.allocation.extra.locations.size.bytes.toNat)
    (reader : UniIndex)
    (lookup : (child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.indexOfTag tracker.global.nextPointerTag=some reader) :
    ParentInterpretation (child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree
      (S05ConcreteProtectedChildCompletion.extend Q.precise.completion reader Q.pointer.grant) := by
  let after := read Q.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed
  have high := GeneralBorrowForestTagHighWater.complete Q.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩ := GenericFunctionTagFormation.fresh_above Q.allocation.extra _ _ tracker.global.nextPointerTag high (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh after.tree.tagMapping tracker.global.nextPointerTag := by rw [P.tags];exact fresh
  obtain ⟨parent,parentAt,_,binding⟩ := Q.binding
  rw [concrete] at binding
  have parentAfter : after.tree.nodeAt Q.pointer.grant=some parent := by change after.tree.nodes.get _=_;rw [P.nodes];exact parentAt
  have tagged : after.tree.indexOfTag tag=some Q.pointer.grant := by rw [binding.2];exact P.runtime.formed.allocator.nodeTags _ _ parentAfter
  have boundsAfter : start.toNat+amount.toNat≤after.tree.locations.size.bytes.toNat := by rw [P.capacity];exact bounds
  have nodesRoom : after.tree.nodes.size+1≤4294967295 := by change after.tree.nodes.data.size+1≤_;rw [P.nodes];exact nodeRoom
  have tagBound : tracker.global.nextPointerTag.value.toNat<(advanced tracker.global room).nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  obtain ⟨_,afterRuntime,_,_,other,otherLookup,leaf,_⟩ := CurrentCallSharedConstructorFrame.metadata after.tree (advanced tracker.global room) P.runtime
    tag tracker.global.nextPointerTag Q.pointer.grant parent tagged parentAfter freshAfter nodesRoom tagBound unheld start amount nonzero boundsAfter
  have equal : other=reader := Option.some.inj (otherLookup.symm.trans lookup)
  subst other
  have primaryLive : ∃ node,after.tree.nodes.get allocationRoot=some node := by
    obtain ⟨node,nodeAt,_⟩ := Q.issued.capability.rootNode
    exact ⟨node,by rw [P.nodes];exact nodeAt⟩
  have parentOrder : parent.tag.value≤tracker.global.nextPointerTag.value :=
    UInt64.le_of_lt (GeneralBorrowParentTagInvariant.parent_below_fresh Q.allocation.extra tracker.global runtime Q.pointer.grant parent parentAt)
  have order := GeneralBorrowSharedChildParentTagOrder.construct after.tree (advanced tracker.global room) P.runtime
    tag tracker.global.nextPointerTag Q.pointer.grant parent tagged parentAfter freshAfter nodesRoom false start amount nonzero boundsAfter P.parents.order parentOrder
  exact CurrentCallParentInsertion.of_leaf after.tree _ Q.precise.completion P.parents reader Q.pointer.grant leaf primaryLive afterRuntime.formed.toGraphState order

variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : Output limits C count) (ready : CurrentCallResourceBodyReadiness.Ready C)

/-- Actual current q resources drive one deterministic shared constructor.
All finite headroom comes from the original readiness budget. -/
theorem construct {nextData nextOwner}
    (Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut)
    (pointer : Q.pointer=CurrentCallResourceSourceAfterBool.pointer out)
    (allocation : Q.allocation=(CurrentCallResourceSourceFinal.entry out).allocation) :
    Nonempty (Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)) := by
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra out.boolOutput.global := by rw [allocation];exact CurrentCallResourceSourceFinal.runtime out
  have distinct : Q.allocation.extra.roots.toList.Nodup := by rw [allocation];exact CurrentCallResourceSourceFinal.roots out
  have short : Q.allocation.extra.nodes.size<65536 := by rw [allocation];exact CurrentCallResourceBodyReadiness.current_short out ready
  have nodeRoom : Q.allocation.extra.nodes.size+1≤4294967295 := by omega
  have concrete : Q.pointer.value.provenance=.concrete id out.sourceOutput.tag := by rw [pointer];rfl
  have last := (Q.window (id,offset+len.toNat-1) ⟨rfl,by have p:=C.positive;omega,by have p:=C.positive;omega⟩).1
  have extent:=Q.issued.capability.extent
  have treeExtent:=Q.issued.capability.treeExtent
  have bounded:=UInt64.toNat_lt Q.allocation.byteSize.bytes
  have fits : offset<2^64 := by have p:=C.positive;omega
  have startEq : (UInt64.ofNat offset).toNat=offset := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fits]
  have bounds : (UInt64.ofNat offset).toNat+len.toNat≤Q.allocation.extra.locations.size.bytes.toNat := by rw [startEq,treeExtent,←extent];have p:=C.positive;omega
  have nonzero : len≠0 := by intro zero;have p:=C.positive;rw [zero] at p;cases p
  obtain ⟨P,done,afterRuntime,capacity,growth,reader,lookup,caps,activity⟩ := CurrentCallResourceDefaultShared.construct Q runtime out.sourceOutput.tag concrete
    (CurrentCallResourceBodyReadiness.current_room out ready) distinct short nodeRoom (UInt64.ofNat offset) len startEq rfl nonzero bounds
  exact ⟨⟨P,done,afterRuntime,capacity,growth,reader,lookup,
    parents Q runtime out.sourceOutput.tag concrete _ _ _ P nodeRoom nonzero bounds reader lookup,caps,activity,
    CurrentCallSharedReadResources.rows Q runtime out.sourceOutput.tag concrete _ _ _ P nodeRoom nonzero bounds reader lookup caps⟩⟩

end
end DuplicatePrefix.CurrentCallResourceSharedResources
