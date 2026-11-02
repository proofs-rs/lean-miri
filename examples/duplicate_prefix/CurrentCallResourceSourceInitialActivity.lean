import duplicate_prefix.CurrentCallResourceEntryFacets
import duplicate_prefix.S03ReturnChildMetadata
import duplicate_prefix.GeneralBorrowConstructorChildActivity
import duplicate_prefix.GeneralBorrowWildcardRootConstructorActivity
import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
import duplicate_prefix.CurrentCallResourceBorrowGrowth

namespace DuplicatePrefix.CurrentCallResourceSourceInitialActivity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowFnEntryRegistration CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

private theorem selected_facets {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (exclusive : demandOf mode=.exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size<65536) (nodeRoom : W.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤W.allocation.extra.locations.size.bytes.toNat)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount=.ok output) :
    DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree (registered tracker.global frame id room).1 ∧
    output.child.tree.locations.size=W.allocation.extra.locations.size ∧
    ∃ child node, output.child.tree.indexOfTag tracker.global.nextPointerTag=some child ∧
      output.child.tree.nodeAt child=some node ∧ node.tag=tracker.global.nextPointerTag ∧
      node.children=#[] ∧ node.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write start (start+amount) := by
  have literalEq : output=CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount := by
    exact Except.ok.inj (actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  obtain ⟨_,held,_,_,_,freshTag⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global frame id room runtime
  let registration := registered tracker.global frame id room
  obtain ⟨_,afterRuntime,_,_,nodes,_,tags,bytes⟩ := CurrentCallResourceFnEntry.prepare_read_selected W runtime frame room exclusive
    distinct short start amount startEq amountEq bounds
  change DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree registration.1 at afterRuntime
  rw [←literalEq] at afterRuntime
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree.nodes=W.allocation.extra.nodes at nodes
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree.tagMapping=W.allocation.extra.tagMapping at tags
  change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global frame id room W.pointer.value.provenance start amount).access.tree.locations.size=W.allocation.extra.locations.size at bytes
  rw [←literalEq] at nodes tags bytes
  have freshAfter : GeneralBorrowTagMap.Fresh output.access.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact freshTag
  have nodeCapacity : output.access.tree.nodes.size+1≤4294967295 := by rw [nodes];exact nodeRoom
  have childBounds : start.toNat+amount.toNat≤output.access.tree.locations.size.bytes.toNat := by rw [bytes];exact bounds
  have tagBound : tracker.global.nextPointerTag.value.toNat<registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag room
    change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag room).value.toNat
    omega
  have tagHeld : registration.1.protectedTags.contains tracker.global.nextPointerTag=true := by unfold ProtectedTags.contains;rw [held];rfl
  have childEq : output.child=output.access.tree.newChild (Size.ofBytes start) (CandidateCurrentWindowPointerChecks.extraOf W.pointer.value.provenance)
    tracker.global.nextPointerTag (DedupRangeMap.new (Size.ofBytes amount) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true := by rw [literalEq];rfl
  cases prov : W.pointer.value.provenance with
  | concrete id parentTag =>
    obtain ⟨parentNode,parentAt,_,binds⟩ := W.binding
    rw [prov] at binds
    have parentAfter : output.access.tree.nodeAt W.pointer.grant=some parentNode := by change output.access.tree.nodes.get _=_;rw [nodes];exact parentAt
    have tagged : output.access.tree.indexOfTag parentTag=some W.pointer.grant := by rw [binds.2];exact afterRuntime.formed.allocator.nodeTags _ _ parentAfter
    have ctor := GeneralBorrowProtectedConstructorRuntime.construct output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag W.pointer.grant parentNode
      tagged parentAfter freshAfter nodeCapacity tagBound tagHeld start amount nonzero childBounds
    obtain ⟨child,node,lookup,present,nodeTag,parent,leaf,hidden,old⟩ := S03ReturnChildMetadata.construct output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag W.pointer.grant parentNode tagged parentAfter freshAfter nodeCapacity start amount nonzero childBounds
    obtain ⟨activeChild,activeLookup,active⟩ := GeneralBorrowConstructorChildActivity.Protected.construct output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag W.pointer.grant parentNode tagged parentAfter freshAfter nodeCapacity start amount nonzero childBounds
    have eqChild : activeChild=child := Option.some.inj (activeLookup.symm.trans lookup)
    subst activeChild
    rw [childEq]
    simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf] using
      And.intro ctor.2.1 (And.intro (ctor.2.2.1.trans bytes) ⟨child,node,lookup,present,nodeTag,leaf,hidden,active⟩)

  | wildcard =>
    have ctor := GeneralBorrowWildcardConstructorRuntime.protected_mutable output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter nodeCapacity tagBound tagHeld
      start amount nonzero childBounds
    obtain ⟨mapping,index,inserted,rows,vacant,graph,monotone,growth⟩ := GeneralBorrowWildcardConstructorSlot.select output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter nodeCapacity (.ReservedFrz false) .None
    have exactTree := GeneralBorrowWildcardConstructorExact.exact output.access.tree afterRuntime.formed.toState tracker.global.nextPointerTag freshAfter nodeCapacity mapping index inserted
      (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl start amount nonzero childBounds
    have present : (GeneralBorrowPositiveWildcardConstructor.result output.access.tree mapping index tracker.global.nextPointerTag (.ReservedFrz false) .None GeneralBorrowFreshChild.inside start amount).nodeAt index = some (WildcardHitZeroConstructor.rootNode tracker.global.nextPointerTag (.ReservedFrz false) .None) := GeneralBorrowFreshLocation.get_same output.access.tree.nodes index _
    have lookup := graph.allocator.nodeTags index _ present
    obtain ⟨activeChild,activeLookup,active⟩ := GeneralBorrowWildcardRootConstructorActivity.construct output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter nodeCapacity start amount nonzero childBounds
    rw [exactTree] at activeLookup active
    have eqChild : activeChild=index := Option.some.inj (activeLookup.symm.trans lookup)
    subst activeChild
    rw [childEq]
    simp only [prov,CandidateCurrentWindowPointerChecks.extraOf]
    refine ⟨ctor.2.1,ctor.2.2.1.trans bytes,?_⟩
    rw [exactTree]
    exact ⟨index,_,lookup,present,rfl,rfl,rfl,active⟩

private theorem window_runtime {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row∈before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag) :
    DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global ∧ W.allocation.extra.roots.toList.Nodup := by
  have present := W.present
  simp only [Present,ActualWorld,Array.toList_map] at present
  obtain ⟨⟨actualId,entry⟩,member,equal⟩ := List.mem_map.mp present
  rcases Prod.mk.inj equal with ⟨rfl,equal⟩
  have treeEq : entry.allocation.extra=W.allocation.extra := congrArg Allocation.extra equal
  exact ⟨⟨by simpa only [treeEq] using state.formed (actualId,entry) member,
    by simpa only [treeEq] using state.coherent (actualId,entry) member,
    by simpa only [treeEq] using state.possible (actualId,entry) member,
    by simpa only [treeEq] using highwater (actualId,entry) member⟩,
    by simpa only [treeEq] using state.roots (actualId,entry) member⟩

variable {options remaining span frames root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span frames root before tracker data owner id offset len W place}
    (out : Output limits C count)

include out in
private theorem source_bounds : (UInt64.ofNat offset).toNat=offset ∧
    (UInt64.ofNat offset).toNat+len.toNat≤W.allocation.extra.locations.size.bytes.toNat := by
  have last := (out.sourceWitness.window (id,offset+len.toNat-1) ⟨rfl,by have p:=C.positive;omega,by have p:=C.positive;omega⟩).1
  have positive := C.positive
  have extent := W.issued.capability.extent
  have treeExtent := W.issued.capability.treeExtent
  have bounded := UInt64.toNat_lt W.allocation.byteSize.bytes
  have fits : offset<2^64 := by omega
  have start : (UInt64.ofNat offset).toNat=offset := by simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fits]
  exact ⟨start,by rw [start,treeExtent,←extent];omega⟩


/-- The SAME actual source constructor supplies q's hidden leaf and Write
activity; no activity field is assumed from BorrowWitness. -/
theorem initial : ∃ node,out.sourceOutput.child.tree.nodes.get out.sourceChild=some node ∧
    node.tag=out.sourceOutput.tag ∧ node.children=#[] ∧ node.isExposed=false ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin out.sourceOutput.child.tree out.sourceChild .Write (UInt64.ofNat offset) (UInt64.ofNat offset+len) := by
  obtain ⟨runtime,distinct⟩ := window_runtime W C.state C.highwater
  obtain ⟨afterRuntime,_,child,node,lookup,present,nodeTag,leaf,hidden,active⟩ := selected_facets W runtime C.borrowFrame C.fresh (by rfl) distinct C.sourceShort
    (by have h:=C.sourceShort;omega) (UInt64.ofNat offset) len (source_bounds out).1 rfl
    (by intro zero;have p:=C.positive;rw [zero] at p;cases p) (source_bounds out).2 out.sourceOutput out.sourceActual
  obtain ⟨actual,actualAt,_,binding⟩ := out.sourceWitness.binding
  change id=id ∧ out.sourceOutput.tag=actual.tag at binding
  have ownLookup : out.sourceOutput.child.tree.indexOfTag tracker.global.nextPointerTag=some out.sourceChild := by
    rw [←out.sourceTag,binding.2]
    exact afterRuntime.formed.allocator.nodeTags _ _ actualAt
  have equal : child=out.sourceChild := Option.some.inj (lookup.symm.trans ownLookup)
  subst child
  exact ⟨node,present,nodeTag.trans out.sourceTag.symm,leaf,hidden,active⟩

end
end DuplicatePrefix.CurrentCallResourceSourceInitialActivity
