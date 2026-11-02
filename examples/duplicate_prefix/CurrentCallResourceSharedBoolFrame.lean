import duplicate_prefix.CurrentCallResourceSharedResources
import duplicate_prefix.CurrentCallReadRootActivity
import duplicate_prefix.CurrentCallSharedReadResources
import duplicate_prefix.CurrentCallResourceBoolFacets

namespace DuplicatePrefix.CurrentCallResourceSharedBoolFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open GeneralBorrowFnEntryRegistration GeneralRangeMapOrigins GeneralBorrowRawSharedExpression
open CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

open CurrentCallResourceSharedResources

private theorem facets {before tracker data owner id offset length}
    (Q : UniformWindow before tracker data owner id offset length .mut)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra tracker.global)
    (tag : BorTag) (concrete : Q.pointer.value.provenance=.concrete id tag)
    (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length)
    (nonzero : amount≠0) (bounds : start.toNat+amount.toNat≤Q.allocation.extra.locations.size.bytes.toNat)
    (nodeCapacity : Q.allocation.extra.nodes.size+1≤4294967295)
    (P : CurrentCallResourceDefaultShared.Preparation Q tag start amount room)
    (target : UniIndex) (node : TreeNode) (present : Q.allocation.extra.nodes.get target=some node)
    (leaf : node.children=#[]) (hidden : node.isExposed=false) (different : target≠Q.pointer.grant)
    (lower upper : UInt64) (active : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra target .Write lower upper) :
    (∃ next,(child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree.nodes.get target=some next ∧
      next.tag=node.tag ∧ next.parent=node.parent ∧ next.children=node.children ∧ next.isExposed=node.isExposed) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin (child Q.allocation.extra tracker.global.protectedTags tag tracker.global.nextPointerTag start amount .VisitChildrenOfAccessed).tree target .Write lower upper := by
  have noWrap : start.toNat+amount.toNat<2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt _)
  have endEq : (start+amount).toNat=start.toNat+amount.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt noWrap]
  have normals : OwnedOn (fun location=>Nonempty (DuplicatePrefixNormalKind.Capability Q.allocation.extra location tracker.global.protectedTags Q.pointer.grant .Read)) start (start+amount) Q.allocation.extra.locations := by
    intro position valid positive beforeUpper afterLower
    have segmentPositive := (GeneralRangeMapGeometry.facts Q.allocation.extra.locations runtime.formed.well (by omega)).2.1 position valid
    have member : Q.allocation.extra.locations.entries[position]∈Q.allocation.extra.locations.entries.toList := Array.mem_toList_iff.mpr (Array.getElem_mem valid)
    have obtainNormal : ∀ byte,Window id offset length byte → Q.allocation.extra.locations.entries[position].range.start.toNat≤byte.2 → byte.2<Q.allocation.extra.locations.entries[position].range.stop.toNat → Nonempty (DuplicatePrefixNormalKind.Capability Q.allocation.extra Q.allocation.extra.locations.entries[position].data tracker.global.protectedTags Q.pointer.grant .Read) := by
      intro byte inside lower upper
      obtain ⟨normal⟩ := CurrentCallResourceAccess.selected_normal Q P.geometry rfl byte inside _ member lower upper (runtime.formed.profile position valid) (runtime.possible position valid)
      exact ⟨DuplicatePrefixNormalKind.of_normal _ _ _ _ normal .Read⟩
    by_cases earlier : start.toNat≤Q.allocation.extra.locations.entries[position].range.start.toNat
    · exact obtainNormal (id,Q.allocation.extra.locations.entries[position].range.start.toNat) ⟨rfl,by omega,by omega⟩ (Nat.le_refl _) segmentPositive
    · exact obtainNormal (id,start.toNat) ⟨rfl,by omega,by omega⟩ (by omega) afterLower
  obtain ⟨parent,parentAt,_,binding⟩ := Q.binding
  rw [concrete] at binding
  have tagged : Q.allocation.extra.indexOfTag tag=some Q.pointer.grant := by rw [binding.2];exact runtime.formed.allocator.nodeTags _ _ parentAt
  have readActive := CurrentCallReadRootActivity.concrete_of_normal Q.allocation.extra tracker.global runtime tag Q.pointer.grant target parent parentAt
    start amount bounds normals tagged node present leaf hidden different lower upper active .VisitChildrenOfAccessed
  let after := read Q.allocation.extra tracker.global.protectedTags tag start amount .VisitChildrenOfAccessed
  have parentAfter : after.tree.nodeAt Q.pointer.grant=some parent := by change after.tree.nodes.get _=_;rw [P.nodes];exact parentAt
  have targetAfter : after.tree.nodes.get target=some node := by rw [P.nodes];exact present
  have taggedAfter : after.tree.indexOfTag tag=some Q.pointer.grant := by rw [binding.2];exact P.runtime.formed.allocator.nodeTags _ _ parentAfter
  have high := GeneralBorrowForestTagHighWater.complete Q.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,_⟩ := GenericFunctionTagFormation.fresh_above Q.allocation.extra _ _ tracker.global.nextPointerTag high (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh after.tree.tagMapping tracker.global.nextPointerTag := by rw [P.tags];exact fresh
  have nodeRoom : after.tree.nodes.size+1≤4294967295 := by
    change after.tree.nodes.data.size+1≤_
    rw [P.nodes]
    exact nodeCapacity
  have boundsAfter : start.toNat+amount.toNat≤after.tree.locations.size.bytes.toNat := by rw [P.capacity];exact bounds
  exact S05SharedConstructorDisjoint.old_facets after.tree (advanced tracker.global room) P.runtime tag tracker.global.nextPointerTag Q.pointer.grant target parent node
    taggedAfter parentAfter targetAfter different freshAfter nodeRoom false start amount nonzero boundsAfter .Write lower upper readActive

variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : Output limits C count) (ready : CurrentCallResourceBodyReadiness.Ready C)

/-- The current Bool resource is retained through the SAME actual shared
Read and constructor, using the disjoint source and Bool byte windows. -/
theorem same {nextData nextOwner}
    (Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut)
    (pointer : Q.pointer=CurrentCallResourceSourceAfterBool.pointer out)
    (allocation : Q.allocation=(CurrentCallResourceSourceFinal.entry out).allocation)
    (completion : Q.precise.completion=CurrentCallResourceSourceFinal.completion out)
    (sameId : out.physical.id=id)
    (stage : Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)) :
    OwnedOn (S05CompletedAncestryReadMutable.Authority
      (child Q.allocation.extra out.boolOutput.global.protectedTags out.sourceOutput.tag out.boolOutput.global.nextPointerTag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree
      (S05ConcreteProtectedChildCompletion.extend Q.precise.completion stage.reader Q.pointer.grant)
      out.boolOutput.global.protectedTags out.boolChild) out.physical.offset (out.physical.offset+1)
      (child Q.allocation.extra out.boolOutput.global.protectedTags out.sourceOutput.tag out.boolOutput.global.nextPointerTag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree.locations := by
  have actualAllocation : Q.allocation=out.updated := by
    rw [allocation,CurrentCallResourceSourceFinal.entry,ite_eq_left sameId]
  have actualCompletion : Q.precise.completion=S05ConcreteProtectedChildCompletion.extend out.R.completion out.boolChild C.V.pointer.grant := by
    rw [completion,CurrentCallResourceSourceFinal.completion,ite_eq_left sameId]
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
  have endFits : (UInt64.ofNat offset).toNat+len.toNat<2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt _)
  have endEq : (UInt64.ofNat offset+len).toNat=offset+len.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt endFits,startEq]
  have nonzero : len≠0 := by intro zero;have p:=C.positive;rw [zero] at p;cases p
  have targetAt : Q.allocation.extra.nodes.get out.boolChild=some out.boolNode := by rw [actualAllocation];exact (CurrentCallResourceBoolFacets.node out).1
  have owned : OwnedOn (S05CompletedAncestryReadMutable.Authority Q.allocation.extra Q.precise.completion out.boolOutput.global.protectedTags out.boolChild)
      out.physical.offset (out.physical.offset+1) Q.allocation.extra.locations := by
    rw [actualAllocation,actualCompletion]
    exact out.afterOwned
  have apart : ∀ point : UInt64,out.physical.offset.toNat≤point.toNat → point.toNat<(out.physical.offset+1).toNat → point.toNat<(UInt64.ofNat offset).toNat ∨ (UInt64.ofNat offset+len).toNat≤point.toNat := by
    intro point lower upper
    rw [startEq,endEq]
    by_cases first : point.toNat<offset
    · exact Or.inl first
    by_cases second : offset+len.toNat≤point.toNat
    · exact Or.inr second
    have overlap : offset≤point.toNat ∧ point.toNat<offset+len.toNat := by omega
    apply False.elim
    have boolUpper : point.toNat<out.physical.offset.toNat+1 := Nat.lt_of_lt_of_le upper (by rw [UInt64.toNat_add];change (out.physical.offset.toNat+1)%(2^64)≤out.physical.offset.toNat+1;exact Nat.mod_le _ _)
    exact C.separate (out.physicalId.symm.trans sameId) (id,point.toNat) ⟨rfl,overlap.1,overlap.2⟩
      ⟨(out.physicalId.symm.trans sameId).symm,by simpa only [out.physicalOffset] using lower,by simpa only [out.physicalOffset] using boolUpper⟩
  obtain ⟨P,_,_,_,_,reader,lookup,_,_,_,retained,_⟩ := CurrentCallResourceDefaultShared.construct_framed Q runtime out.sourceOutput.tag concrete
    (CurrentCallResourceBodyReadiness.current_room out ready) distinct short nodeRoom (UInt64.ofNat offset) len startEq rfl nonzero bounds
    out.boolChild out.boolNode targetAt out.physical.offset (out.physical.offset+1) apart owned
  have eqReader : reader=stage.reader := Option.some.inj (lookup.symm.trans stage.lookup)
  subst reader
  exact retained

theorem same_facets {nextData nextOwner}
    (Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut)
    (pointer : Q.pointer=CurrentCallResourceSourceAfterBool.pointer out)
    (allocation : Q.allocation=(CurrentCallResourceSourceFinal.entry out).allocation)
    (sameId : out.physical.id=id)
    (stage : Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)) :
    (∃ next,(child Q.allocation.extra out.boolOutput.global.protectedTags out.sourceOutput.tag out.boolOutput.global.nextPointerTag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree.nodes.get out.boolChild=some next ∧
      next.tag=out.boolNode.tag ∧ next.parent=out.boolNode.parent ∧ next.children=out.boolNode.children ∧ next.isExposed=out.boolNode.isExposed) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin (child Q.allocation.extra out.boolOutput.global.protectedTags out.sourceOutput.tag out.boolOutput.global.nextPointerTag (UInt64.ofNat offset) len .VisitChildrenOfAccessed).tree out.boolChild .Write out.physical.offset (out.physical.offset+1) := by
  have actualAllocation : Q.allocation=out.updated := by
    rw [allocation,CurrentCallResourceSourceFinal.entry,ite_eq_left sameId]
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
  have endFits : (UInt64.ofNat offset).toNat+len.toNat<2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt _)
  have endEq : (UInt64.ofNat offset+len).toNat=offset+len.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt endFits,startEq]
  have nonzero : len≠0 := by intro zero;have p:=C.positive;rw [zero] at p;cases p
  have targetAt : Q.allocation.extra.nodes.get out.boolChild=some out.boolNode := by rw [actualAllocation];exact (CurrentCallResourceBoolFacets.node out).1
  obtain ⟨sourceNode,sourceAt,_,binding⟩ := Q.binding
  rw [concrete] at binding
  have different : out.boolChild≠Q.pointer.grant := by
    intro equal
    have targetAt' : Q.allocation.extra.nodes.get Q.pointer.grant=some out.boolNode := by rw [←equal];exact targetAt
    have sameNode : out.boolNode=sourceNode := Option.some.inj (targetAt'.symm.trans sourceAt)
    have sourceTagEq : out.boolNode.tag=out.sourceOutput.tag := sameNode ▸ binding.2.symm
    have next := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag C.fresh
    have tags : out.sourceOutput.tag.value.toNat=tracker.global.nextPointerTag.value.toNat := congrArg (fun tag : BorTag=>tag.value.toNat) out.sourceTag
    have btag := congrArg (fun tag : BorTag=>tag.value.toNat) ((CurrentCallResourceBoolFacets.node out).2.1.symm.trans sourceTagEq)
    rw [out.sourceGlobal] at btag
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag C.fresh).value.toNat=out.sourceOutput.tag.value.toNat at btag
    omega
  apply facets Q runtime out.sourceOutput.tag concrete _ (UInt64.ofNat offset) len startEq rfl nonzero bounds nodeRoom stage.preparation
    out.boolChild out.boolNode targetAt (CurrentCallResourceBoolFacets.current out).1 (CurrentCallResourceBoolFacets.current out).2.1 different out.physical.offset (out.physical.offset+1)
  rw [actualAllocation]
  exact (CurrentCallResourceBoolFacets.current out).2.2.2

/-- In the different-allocation case the shared operation has no Bool-tree
step or protector registration; its current rows and flags remain literal. -/
theorem different (_different : out.physical.id≠id) :
    OwnedOn (S05CompletedAncestryReadMutable.Authority out.updated.extra
      (S05ConcreteProtectedChildCompletion.extend out.R.completion out.boolChild C.V.pointer.grant)
      out.boolOutput.global.protectedTags out.boolChild) out.physical.offset (out.physical.offset+1) out.updated.extra.locations := out.afterOwned

/-- The untouched different-allocation Bool tree retains its actual hidden
leaf and Write activity as well as its rows. -/
theorem different_facets (_different : out.physical.id≠id) :
    out.updated.extra.nodes.get out.boolChild=some out.boolNode ∧
    out.boolNode.tag=out.sourceOutput.global.nextPointerTag ∧
    out.boolNode.children=#[] ∧ out.boolNode.isExposed=false ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin out.updated.extra out.boolChild .Write out.physical.offset (out.physical.offset+1) := by
  exact ⟨(CurrentCallResourceBoolFacets.node out).1,(CurrentCallResourceBoolFacets.node out).2.1,
    (CurrentCallResourceBoolFacets.current out).1,(CurrentCallResourceBoolFacets.current out).2.1,(CurrentCallResourceBoolFacets.current out).2.2.2⟩

end
end DuplicatePrefix.CurrentCallResourceSharedBoolFrame
