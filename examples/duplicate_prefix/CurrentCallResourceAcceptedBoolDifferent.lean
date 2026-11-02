import duplicate_prefix.CurrentCallResourceAcceptedCopy
import duplicate_prefix.CurrentCallResourceAsMutBoolCurrent

namespace DuplicatePrefix.CurrentCallResourceAcceptedBoolDifferent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    {out : Output limits C count} {ready : CurrentCallResourceBodyReadiness.Ready C} {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    {result : CurrentCallResourceLenReturn.Result out ready Q stage}
    (done : CurrentCallResourceAsMutInvoke.DefaultResult result)
    (fresh : done.nextTracker.global.nextPointerTag.value<18446744073709551615)
    (valid15 : (15 : MIR.LocalId)<done.frame.locals.size)
    (seed : CurrentCallResourceAsMutCall.Seed options limits remaining span done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15)
    (returned : CurrentCallResourceAsMutReturn.Returned done.current done.entry done.frame done.base
      (CurrentCallResourceLenReturn.postTracker out ready).global.nextPointerTag fresh valid15 seed)
    (copied : CurrentCallResourceAcceptedCopy.Result done fresh valid15 seed returned)
    (P : CurrentCallResourceAsMutBoolCurrent.Packet result done fresh valid15 seed returned)
    (different : out.physical.id≠id)

include different in
/-- Only the source allocation is replaced by the actual copy; the original
Bool allocation remains present, with no allocation-identity change. -/
theorem present : Present (ActualWorld copied.machine) out.physical.id P.B.allocation := by
  have old:=P.B.present
  simp only [Present,ActualWorld,Array.toList_map] at old ⊢
  obtain ⟨row,member,equal⟩:=List.mem_map.mp old
  have rowId : row.1=out.physical.id:=congrArg Prod.fst equal
  have memory:=congrArg MemoryState.live copied.memory
  dsimp only [CanonicalCopy.replaceAllocation,Storage.withCurrent] at memory
  rw [(AddOutput.preserved options remaining span returned.machine).1] at memory
  rw [memory]
  apply List.mem_map.mpr
  refine ⟨row,?_,equal⟩
  apply Array.mem_toList_iff.mpr
  apply Array.mem_push_of_mem
  apply Array.mem_filter.mpr
  exact ⟨Array.mem_toList_iff.mp member,by simp [rowId,different]⟩

include different in
private theorem issued {grant : UniIndex}
    (old : SpatialDelegation returned.machine (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed) out.physical.id
      P.B.allocation P.B.precise.completion grant) :
    SpatialDelegation copied.machine (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed) out.physical.id
      P.B.allocation P.B.precise.completion grant := by
  apply CurrentCallAllocationLicense.spatial old copied.machine (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed)
    P.B.allocation (present done fresh valid15 seed returned copied P different) rfl rfl rfl rfl
  · intro position root found
    exact found
  · intro index node found
    exact ⟨node,found,rfl,rfl,rfl,rfl⟩
  · intro root origin edge
    exact edge

include different in
/-- The actual different-allocation copy keeps every Bool family/owner/loan,
value, optional-parent map, and allocation fixed in its real post-world. -/
theorem current : ∃ B : UniformWindow copied.machine (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed)
    P.identities P.holder out.physical.id out.physical.offset.toNat 1 .ret,
      B.pointer=P.B.pointer ∧ B.allocation=P.B.allocation ∧ B.precise=P.B.precise ∧ B.loan=P.B.loan := by
  let B : UniformWindow copied.machine (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed)
      P.identities P.holder out.physical.id out.physical.offset.toNat 1 .ret := {
    loan:=P.B.loan,pointer:=P.B.pointer,allocation:=P.B.allocation,precise:=P.B.precise,
    loanAt:=P.B.loanAt,pointerAt:=P.B.pointerAt,pointerId:=P.B.pointerId,
    present:=present done fresh valid15 seed returned copied P different,preciseAt:=P.B.preciseAt,binding:=P.B.binding,
    issued:=issued done fresh valid15 seed returned copied P different P.B.issued,parents:=P.B.parents,window:=P.B.window}
  exact ⟨B,rfl,rfl,rfl,rfl⟩

include different in
theorem parent_issued : SpatialDelegation copied.machine (CurrentCallResourceAcceptedCopy.held done fresh valid15 seed) out.physical.id
    P.B.allocation P.B.precise.completion C.V.pointer.grant :=
  issued done fresh valid15 seed returned copied P different P.parentIssued

theorem parent_binding : PointerBinds P.B.allocation C.V.pointer := P.parentBinding

theorem edge : P.B.precise.completion.parents[P.B.pointer.grant.toNat]?=some (some C.V.pointer.grant) := P.edge

end
end DuplicatePrefix.CurrentCallResourceAcceptedBoolDifferent
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceAcceptedBoolDifferent" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual different Bool copy dependency {dependency}"
