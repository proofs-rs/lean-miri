import duplicate_prefix.CurrentCallSpatialEntryBoolCurrent
import duplicate_prefix.CurrentCallEmptyEntryReturnWindow
namespace DuplicatePrefix.CurrentCallSpatialEntryBoolPhysical
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallSpatialCover CurrentCallSpatialEntry CurrentCallSpatialEntryBoolCurrent
open CanonicalConfigFacts ActualReferenceContext GeneralBorrowFnEntryRegistration TypedBorrowSteps ReturnProtection RootFrameData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
private theorem mutation_extra (allocation updated : Allocation Provenance BorrowTree) (tree : BorrowTree)
    (offset : UInt64) (extra : updated.extra=tree)
    (actual : Allocation.writeUninit (allocRange (Size.ofBytes offset) (Size.ofBytes 1)) (Size.ofBytes 8) (allocation.setExtra tree)=.ok () updated) :
    Allocation.writeUninit (allocRange (Size.ofBytes offset) (Size.ofBytes 1)) (Size.ofBytes 8) (allocation.setExtra updated.extra)=.ok () updated := by
  rw [extra];exact actual

variable {options remaining span frames root before tracker ctx offset len source returnOffset ret place}
    {C : Conditions options remaining span frames root before tracker ctx offset len source returnOffset ret place}
    {limits count} (out : Output C limits count)

def sourceMachine := CurrentCallSpatialSourceInstall.copiedMachine source C.borrowFrame C.fresh (UInt64.ofNat offset) len out.entry

theorem id_eq : out.physical.id=C.physical.id := (physical_id out).trans C.physicalId.symm
theorem offset_eq : out.physical.offset=C.physical.offset := UInt64.toNat_inj.mp (out.physicalOffset.trans C.physicalOffset.symm)
theorem pointer_eq : out.physical.pointer=C.physical.pointer :=
  out.physicalPointer.trans ((congrArg Family.value out.returnFamily).trans C.returnPointer.symm)

private theorem initial_binding : CandidateCallBindings.WindowBinding (sourceMachine out) out.physical.pointer out.physical.id out.physical.offset.toNat 1 := by
  have framed:=CurrentCallBoolWindow.replace_binding before (sourceMachine out) C.physical.pointer C.physical.id C.physical.offset.toNat 1
    C.returnBinding source.backing.id out.entry {out.entry with allocation:=out.entry.allocation.setExtra (sourceOutput C).child.tree}
    out.sourceLive rfl rfl rfl rfl
  rw [pointer_eq out,id_eq out,offset_eq out]
  exact framed

private theorem initial_ready : CurrentCallBoolProtection.WindowReady (sourceMachine out) out.physical.id out.physical.offset.toNat 1 := by
  rw [id_eq out,offset_eq out]
  exact C.ready.transport rfl

/-- Determinism recovers the storage mutation from the SAME actual Bool
operation and entry control result. This adds no interpreter step. -/
theorem mutation : Allocation.writeUninit (allocRange (Size.ofBytes out.physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
    (out.physical.entry.allocation.setExtra out.updated.extra)=.ok () out.updated := by
  obtain ⟨retagCtx⟩:=(DuplicatePrefixCallModel.contexts options remaining span before C.model).2.2.2
  have frameBool : (atSpan (argsRoot C count) ⟨601⟩).frame.extra.borrowTracker=some (sourceOutput C).frame := by
    exact CurrentCallSourceArguments.result_borrowFrame options remaining span root C.borrowFrame source.family.value len count source.backing.id tracker.global.nextPointerTag
  have short : out.physical.entry.allocation.extra.nodes.size+1<65536 := by
    rw [(spatial_install_rule ".CurrentCallSpatialEntryBoolCurrent.allocation_eq") out]
    exact (spatial_install_rule ".CurrentCallSpatialEntryBoolCurrent.old_runtime") out |>.2.2
  obtain ⟨output,child,actual,tag,global,frame,⟨witness⟩,updated,protect,extra,size,length,mutable,mutation,snapshot,tracked,frameTracked,returnPlace⟩ :=
    CurrentCallSpatialBoolActivation.activate options limits (remaining+1) span retagCtx (sourceMachine out)
      ⟨(sourceOutput C).global,tracker.retagMode⟩ _ returnOffset out.dst frames (atSpan (argsRoot C count) ⟨601⟩).frame (sourceOutput C).frame
      out.sourceTracked ((spatial_install_rule ".CurrentCallSpatialEntryBoolCurrent.source_highwater") out) frameBool
      place out.physical out.physicalId out.physicalOffset out.physicalPointer (initial_binding out) out.fresh short
      rfl C.model.noDataRace C.model.noBackend (initial_ready out)
  have outputEq : output=out.boolOutput:=Except.ok.inj (actual.symm.trans out.boolActual)
  subst output
  let final:=CurrentCallSpatialEntry.finalMachine place _ out.physical
    (CurrentCallSpatialEntry.protectedState C count out.entry out.physical out.fresh out.boolOutput) updated
  have finish:=CurrentCallSpatialEntryControl.finish_of_arguments options limits remaining span frames root C.rawLocals
    C.borrowFrame source.family.value len count source.backing.id tracker.global.nextPointerTag before (sourceMachine out) final
    (sourceOutput C).frame out.physical.id (sourceOutput C).global.nextPointerTag place out.arguments protect
  have states := (EStateM.Result.ok.inj (finish.1.symm.trans out.actual)).2
  have memoryEq:=congrArg (fun state : RootState=>state.machine.memory) states
  change final.memory=(machine out).memory at memoryEq
  have nextLive : final.memory.live.find? (fun row=>row.1==out.physical.id)=some (out.physical.id,{out.physical.entry with allocation:=updated}) :=
    MemoryCopyBridge.live_lookup_replaced _ _ _
  have nextLive' : (machine out).memory.live.find? (fun row=>row.1==out.physical.id)=some (out.physical.id,{out.physical.entry with allocation:=updated}) := by
    rw [←memoryEq];exact nextLive
  have entries := (Prod.mk.inj (Option.some.inj (nextLive'.symm.trans (live out)))).2
  have updatedEq : updated=out.updated:=congrArg LocalAllocation.allocation entries
  rw [updatedEq] at mutation extra
  exact mutation_extra out.physical.entry.allocation out.updated _ out.physical.offset extra mutation

private theorem memory : (machine out).memory.live=((sourceMachine out).memory.live.filter (fun row=>row.1!=out.physical.id)).push
    (out.physical.id,{out.physical.entry with allocation:=out.updated}) := by
  exact congrArg MemoryState.live (MemoryCopyBridge.live_update_twice (sourceMachine out).memory out.physical.id
    {out.physical.entry with allocation:=out.physical.entry.allocation.setExtra out.boolOutput.child.tree}
    {out.physical.entry with allocation:=out.updated})

theorem binding : CandidateCallBindings.WindowBinding (machine out) out.physical.pointer out.physical.id out.physical.offset.toNat 1 :=
  CurrentCallBoolWindow.replace_binding (sourceMachine out) (machine out) out.physical.pointer out.physical.id out.physical.offset.toNat 1
    (initial_binding out) out.physical.id out.physical.entry {out.physical.entry with allocation:=out.updated}
    out.physical.live out.updatedLength out.updatedSize rfl (memory out)

/-- The original return pointer, not the temporary child pointer, supplies the
actual post-clear scalar destination window. Its initial Bool value is unused. -/
theorem current : ∃window : CurrentCallBoolScalarWrite.Window (machine out) place,
    window.pointer=C.physical.pointer ∧window.id=C.physical.id ∧window.offset=C.physical.offset ∧
    window.entry={out.physical.entry with allocation:=out.updated} ∧
    CandidateCallBindings.WindowBinding (machine out) window.pointer window.id window.offset.toNat 1 ∧
    CurrentCallBoolProtection.WindowReady (machine out) window.id window.offset.toNat 1 := by
  have updatedSelf : out.updated.setExtra out.updated.extra=out.updated := by cases out.updated;rfl
  have nextLive : (machine out).memory.live.find? (fun row=>row.1==out.physical.id)=
      some (out.physical.id,{out.physical.entry with allocation:=out.updated.setExtra out.updated.extra}) := by
    rw [updatedSelf];exact live out
  obtain ⟨window,pointer,id,offset,entry,binding,ready⟩:=CurrentCallEmptyEntryReturnWindow.of_mutation out.physical
    out.updated.extra out.updated.extra out.updated (mutation out) nextLive rfl (binding out) (initial_ready out) rfl
  exact ⟨window,pointer.trans (pointer_eq out),id.trans (id_eq out),offset.trans (offset_eq out),
    by rw [entry,updatedSelf],binding,ready⟩

end
end DuplicatePrefix.CurrentCallSpatialEntryBoolPhysical
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialEntryBoolPhysical" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial entry Bool physical dependency {dependency}"
