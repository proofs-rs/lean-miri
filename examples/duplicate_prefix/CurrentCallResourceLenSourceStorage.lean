import duplicate_prefix.CurrentCallResourceEntrySourceStorage
import duplicate_prefix.CurrentCallResourceLenReturn

namespace DuplicatePrefix.CurrentCallResourceLenSourceStorage
open Miri Miri.Input Miri.ABI Miri.Memory Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- The same actual source row after shared construction, helper access,
protector release and pop retains the accepted-copy storage packet. -/
theorem of_return {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : Output limits C count) (ready : CurrentCallResourceBodyReadiness.Ready C)
    {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len
      (CurrentCallResourceBodyReadiness.current_room out ready)}
    (returned : CurrentCallResourceLenReturn.Result out ready Q stage)
    (physical : OrdinaryPhysicalValidity.MutU8Slice W.allocation (UInt64.ofNat offset) len)
    (room : W.allocation.len+64<2^64) :
    let entry := {(CurrentCallResourceLenInvoke.entry out) with allocation :=
      (CurrentCallResourceLenInvoke.entry out).allocation.setExtra (CurrentCallResourceLenReturn.releasedTree out ready)}
    returned.machine.memory.live.find? (fun row=>row.1==id)=some (id,entry) ∧
      CurrentCallResourceEntrySourceStorage.Data entry.allocation (UInt64.ofNat offset) len := by
  have initial:=CurrentCallResourceEntrySourceStorage.of_entry out physical room
  have shared:=initial.set_extra (CurrentCallResourceSharedStage.tree out)
  have current:=shared.set_extra (CurrentCallResourceLenReturn.releasedTree out ready)
  refine ⟨returned.sourceLive,?_⟩
  simpa only [CurrentCallResourceLenInvoke.entry] using current

end
end DuplicatePrefix.CurrentCallResourceLenSourceStorage
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceLenSourceStorage" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual returned source storage dependency {dependency}"
