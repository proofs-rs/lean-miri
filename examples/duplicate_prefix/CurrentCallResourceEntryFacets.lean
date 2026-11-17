import duplicate_prefix.CurrentCallResourceSourceFinal
import duplicate_prefix.CurrentCallResourceBorrowGrowth

namespace DuplicatePrefix.CurrentCallResourceEntryFacets
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowFnEntryRegistration CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

private theorem selected_growth {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (frame : FrameState) (room : tracker.global.nextPointerTag.value<18446744073709551615)
    (exclusive : demandOf mode=.exclusive) (distinct : W.allocation.extra.roots.toList.Nodup)
    (short : W.allocation.extra.nodes.size<65536) (nodeRoom : W.allocation.extra.nodes.size+1≤4294967295)
    (start amount : UInt64) (startEq : start.toNat=offset) (amountEq : amount.toNat=length) (nonzero : amount≠0)
    (bounds : start.toNat+amount.toNat≤W.allocation.extra.locations.size.bytes.toNat)
    (output : GeneralBorrowForestFnEntry.Output)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global frame id W.pointer.value.provenance start amount=.ok output) :
    output.child.tree.nodes.size ≤ W.allocation.extra.nodes.size + 1 := by
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
    rw [childEq]
    simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf,nodes] using ctor.2.2.2
  | wildcard =>
    have ctor := GeneralBorrowWildcardConstructorRuntime.protected_mutable output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter nodeCapacity tagBound tagHeld
      start amount nonzero childBounds
    rw [childEq]
    simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf,nodes] using ctor.2.2.2.1


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

theorem source_growth : out.sourceOutput.child.tree.nodes.size≤W.allocation.extra.nodes.size+1 := by
  obtain ⟨runtime,distinct⟩ := window_runtime W C.state C.highwater
  exact CurrentCallResourceBorrowGrowth.operation W runtime C.state C.highwater C.borrowFrame C.fresh (by rfl) distinct C.sourceShort
    (by have h:=C.sourceShort;omega) (UInt64.ofNat offset) len (source_bounds out).1 rfl
    (by intro zero;have p:=C.positive;rw [zero] at p;cases p) (source_bounds out).2 out.sourceOutput out.sourceActual

private def rolePrecise : PreciseAllocation := {C.V.precise with completion:=out.R.completion}
private def roleData : Identities :=
  {data with interpretation:={data.interpretation with precise:=data.interpretation.precise.push (C.physical.id,rolePrecise out)}}
private def boolRole : UniformWindow out.sourceMachine ⟨out.sourceOutput.global,tracker.retagMode⟩ (roleData out)
    C.returnOwner C.physical.id C.physical.offset.toNat 1 .ret where
  loan:=C.V.loan
  pointer:=C.V.pointer
  allocation:=C.V.allocation.setExtra out.R.tree
  precise:=rolePrecise out
  loanAt:=C.V.loanAt
  pointerAt:=C.V.pointerAt
  pointerId:=C.V.pointerId
  present:=out.R.present
  preciseAt:=Array.mem_toList_iff.mpr (Array.mem_push.mpr (.inr rfl))
  binding:=out.R.binding
  issued:=out.R.issued
  parents:=out.R.parents
  window:=out.R.window

private theorem role_runtime : DuplicatePrefixBorrowContract.RuntimeFacts out.R.tree out.sourceOutput.global ∧
    out.R.tree.roots.toList.Nodup ∧ out.R.tree.nodes.size<65536 := by
  by_cases same : C.physical.id=id
  · have trees:=out.sameTree same
    have growth:=source_growth out
    have room:=C.boolRoom
    rw [C.sameAllocation same] at room
    rw [trees.1]
    refine ⟨out.sourceWitness.runtime,?_,by omega⟩
    obtain ⟨runtime,distinct⟩ := window_runtime W C.state C.highwater
    exact CurrentCallResourceSourceKeyOrigin.roots W runtime C.state C.highwater C.borrowFrame C.fresh (by rfl) distinct C.sourceShort
      (by have h:=C.sourceShort;omega) (UInt64.ofNat offset) len (source_bounds out).1 rfl
      (by intro zero;have p:=C.positive;rw [zero] at p;cases p) (source_bounds out).2 out.sourceOutput out.sourceActual
  · obtain ⟨runtime,distinct⟩ := window_runtime C.V C.state C.highwater
    have current := (GeneralBorrowFnEntryRegistrationRuntime.prepare C.V.allocation.extra tracker.global C.borrowFrame id C.fresh runtime).2.2.2.1
    rw [(out.otherTree same).1]
    refine ⟨?_,distinct,by have room:=C.boolRoom;omega⟩
    rw [out.sourceGlobal]
    exact current

theorem bool_growth : out.boolOutput.child.tree.nodes.size≤out.R.tree.nodes.size+1 := by
  let B:=boolRole out
  have actual : CandidateCurrentFnEntryRaw.operation B.allocation.extra out.sourceOutput.global out.sourceOutput.frame C.physical.id
      B.pointer.value.provenance out.physical.offset 1=.ok out.boolOutput := by
    simpa only [B,boolRole,Allocation.setExtra,Allocation.mapExtra,out.physicalId] using out.boolActual
  have bounds : out.physical.offset.toNat+1≤B.allocation.extra.locations.size.bytes.toNat := by
    have first := (B.window (C.physical.id,out.physical.offset.toNat)
      ⟨rfl,by rw [out.physicalOffset];exact Nat.le_refl _,by rw [out.physicalOffset];omega⟩).1
    rw [B.issued.capability.treeExtent,←B.issued.capability.extent]
    omega
  have short : B.allocation.extra.nodes.size<65536 := (role_runtime out).2.2
  have growth:=selected_growth B (role_runtime out).1 out.sourceOutput.frame out.returnRoom (by rfl)
    (role_runtime out).2.1 (role_runtime out).2.2 (by omega)
    out.physical.offset 1 (congrArg UInt64.toNat out.physicalOffset) rfl (by decide) bounds out.boolOutput actual
  exact growth

/-- Actual allocator growth only. These inequalities do not imply additional
16-bit traversal headroom beyond the INITIAL readiness assumptions. -/
theorem current_growth : (CurrentCallResourceSourceFinal.entry out).allocation.extra.nodes.size≤
    W.allocation.extra.nodes.size+(if out.physical.id=id then 2 else 1) := by
  have source:=source_growth out
  by_cases same : out.physical.id=id
  · have current:=bool_growth out
    have trees:=out.sameTree (out.physicalId.symm.trans same)
    rw [trees.1] at current
    simpa only [CurrentCallResourceSourceFinal.entry,ite_eq_left same,out.updatedNodes] using Nat.le_trans current (by omega)
  · simpa only [CurrentCallResourceSourceFinal.entry,ite_eq_right same,out.sourceAllocation,Allocation.setExtra,Allocation.mapExtra] using source

theorem current_node_room : (CurrentCallResourceSourceFinal.entry out).allocation.extra.nodes.size+1≤4294967295 := by
  have growth:=current_growth out
  have short:=C.sourceShort
  split at growth <;> omega

theorem same_short (same : out.physical.id=id) :
    (CurrentCallResourceSourceFinal.entry out).allocation.extra.nodes.size<65536 := by
  have growth:=current_growth out
  simp only [ite_eq_left same] at growth
  have room:=C.boolRoom
  rw [C.sameAllocation (out.physicalId.symm.trans same)] at room
  omega

theorem tag_growth : out.boolOutput.global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+2 := by
  have first:=GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag C.fresh
  have second:=GenericFunctionEntryNumerics.successor_value out.sourceOutput.global.nextPointerTag out.returnRoom
  change (advanced tracker.global C.fresh).nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+1 at first
  change (advanced out.sourceOutput.global out.returnRoom).nextPointerTag.value.toNat=out.sourceOutput.global.nextPointerTag.value.toNat+1 at second
  have source : out.sourceOutput.global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+1 := by
    rw [out.sourceGlobal]
    exact first
  rw [out.boolGlobal]
  change (advanced out.sourceOutput.global out.returnRoom).nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+2
  omega

/-- The actual current q tag is read from the retained concrete instance. No
leaf or restored caller-parent permission is assumed. -/
theorem q_node : ∃ node,(CurrentCallResourceSourceFinal.entry out).allocation.extra.nodes.get out.sourceChild=some node ∧ node.tag=out.sourceOutput.tag := by
  obtain ⟨node,present,mapped,binding⟩ := CurrentCallResourceSourceFinal.binding out
  change id=id ∧ out.sourceOutput.tag=node.tag at binding
  exact ⟨node,present,binding.2.symm⟩

theorem capacity : (CurrentCallResourceSourceFinal.entry out).allocation.extra.locations.size=
    (CurrentCallResourceSourceFinal.entry out).allocation.byteSize ∧
    (CurrentCallResourceSourceFinal.entry out).allocation.len=(CurrentCallResourceSourceFinal.entry out).allocation.byteSize.bytes.toNat := by
  have cap:=(CurrentCallResourceSourceFinal.issued out).capability
  exact ⟨cap.treeExtent,cap.extent⟩

end
end DuplicatePrefix.CurrentCallResourceEntryFacets
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallResourceEntryFacets.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved entry facets dependency {dependency}"
