import duplicate_prefix.CurrentCallResourceLenReturn
import duplicate_prefix.CurrentCallResourceRootPhysical
import duplicate_prefix.CurrentCallScalarTreeWindow
namespace DuplicatePrefix.CurrentCallResourceLenPhysical
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization CurrentCallResourceEntryBody
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section
variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    {out : Output limits C count} {ready : CurrentCallResourceBodyReadiness.Ready C} {nextData nextOwner}
    {Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩ nextData nextOwner id offset len.toNat .mut}
    {stage : CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len (CurrentCallResourceBodyReadiness.current_room out ready)}
    (result : CurrentCallResourceLenReturn.Result out ready Q stage)

theorem memory : result.machine.memory.live=(out.finalMachine.memory.live.filter (fun row=>row.1!=id)).push
    (id,{(CurrentCallResourceSourceFinal.entry out) with allocation:=
      (CurrentCallResourceSourceFinal.entry out).allocation.setExtra (CurrentCallResourceLenReturn.releasedTree out ready)}) := by
  rw [result.memory]
  exact congrArg (fun memory=>memory.live) (MemoryCopyBridge.live_update_twice out.finalMachine.memory id
    {(CurrentCallResourceSourceFinal.entry out) with allocation:=(CurrentCallResourceSourceFinal.entry out).allocation.setExtra (CurrentCallResourceSharedStage.tree out)}
    {(CurrentCallResourceSourceFinal.entry out) with allocation:=(CurrentCallResourceSourceFinal.entry out).allocation.setExtra (CurrentCallResourceLenReturn.releasedTree out ready)})

theorem of_return : ∃ window : CurrentCallBoolScalarWrite.Window result.machine place,
    window.pointer=C.physical.pointer ∧ window.id=C.physical.id ∧ window.offset=C.physical.offset ∧
    CandidateCallBindings.WindowBinding result.machine window.pointer window.id window.offset.toNat 1 := by
  obtain ⟨old,pointer,idEq,offsetEq,binding⟩:=CurrentCallResourceRootPhysical.of_entry out
  have addresses : result.machine.user.addresses=out.finalMachine.user.addresses := by
    rw [result.flags.addresses,result.helper.addresses]
    exact CurrentCallResourceSharedStage.addresses out
  have live:=CurrentCallResourceSourceFinal.live out
  obtain ⟨next,nextPointer,nextId,nextOffset,nextBinding⟩:=CurrentCallScalarTreeWindow.replace old binding id
    (CurrentCallResourceSourceFinal.entry out) (CurrentCallResourceLenReturn.releasedTree out ready)
    live addresses (memory result)
  exact ⟨next,nextPointer.trans pointer,nextId.trans idEq,nextOffset.trans offsetEq,nextBinding⟩
end
end DuplicatePrefix.CurrentCallResourceLenPhysical
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceLenPhysical" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual Len physical dependency {dependency}"
