import duplicate_prefix.CurrentCallResourceSharedResources

namespace DuplicatePrefix.CurrentCallResourceSharedInvoke
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows CandidateStableCallOwnership CandidateCurrentJointCall
open CurrentCallResourceNormalization CurrentCallResourceEntryBody ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
noncomputable section

variable {options remaining span root before tracker data owner id offset len W place limits count}
    {C : Conditions options remaining span #[] root before tracker data owner id offset len W place}
    (out : Output limits C count) (ready : CurrentCallResourceBodyReadiness.Ready C)

/-- The actual nonzero root prefix and shared-Ref statement consume one current
resource window. Both operational certificates are derived internally from the
same Read/constructor stage retained for the ensuing Len helper. -/
theorem invoke_with_address (nonzero : count≠0) :
    ∃ (frame : CompilerFrameContext.ActualFrame), ∃ nextData nextOwner,
      ∃ Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩
          nextData nextOwner id offset len.toNat .mut,
        ∃ shape : GenericFunctionEntryPrefix.Shape (CurrentCallResourceEntry.finishedFrame out) frame count,
          Q.pointer=CurrentCallResourceSourceAfterBool.pointer out ∧
          Q.allocation=(CurrentCallResourceSourceFinal.entry out).allocation ∧
          Q.precise.completion=CurrentCallResourceSourceFinal.completion out ∧
          Nonempty (CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len
            (CurrentCallResourceBodyReadiness.current_room out ready)) ∧
          ∃ base : UInt64,
            (CurrentCallResourceSharedStage.machine out).user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩ ∧
            (CurrentCallResourceSourceAfterBool.pointer out).value=
              Pointer.new (.concrete id out.sourceOutput.tag) (Size.ofBytes (base+UInt64.ofNat offset)) ∧
            base+UInt64.ofNat offset≠0 ∧
            SuccessfulTrace.Trace (config options (remaining+1) span) limits
              (Storage.withCurrent #[] (CurrentCallResourceEntry.finishedFrame out) out.finalMachine)
              (Storage.withCurrent #[]
                (CurrentCallResourceSharedStage.afterFrame out frame (by rw [shape.size];decide) base)
                (CurrentCallResourceSharedStage.afterMachine out ready)) := by
  obtain ⟨frame,initialTrace,shape,nextData,nextOwner,Q,pointer,allocation,completion⟩ :=
    CurrentCallResourceSharedStage.before_shared out nonzero
  obtain ⟨stage⟩ := CurrentCallResourceSharedResources.construct out ready Q pointer allocation
  have readDone:=stage.preparation.completed
  have childDone:=stage.done
  rw [allocation] at readDone childDone
  obtain ⟨base,cached,address,nonnull,actual⟩:=CurrentCallResourceSharedStage.step_of_steps_with_address out ready frame shape readDone childDone
  exact ⟨frame,nextData,nextOwner,Q,shape,pointer,allocation,completion,⟨stage⟩,base,cached,address,nonnull,
    SuccessfulTrace.append initialTrace (.next actual (.refl _))⟩

theorem invoke (nonzero : count≠0) :
    ∃ (frame : CompilerFrameContext.ActualFrame), ∃ nextData nextOwner,
      ∃ Q : UniformWindow (CurrentCallResourceSharedStage.machine out) ⟨out.boolOutput.global,tracker.retagMode⟩
          nextData nextOwner id offset len.toNat .mut,
        ∃ shape : GenericFunctionEntryPrefix.Shape (CurrentCallResourceEntry.finishedFrame out) frame count,
          Q.pointer=CurrentCallResourceSourceAfterBool.pointer out ∧
          Q.allocation=(CurrentCallResourceSourceFinal.entry out).allocation ∧
          Q.precise.completion=CurrentCallResourceSourceFinal.completion out ∧
          Nonempty (CurrentCallResourceSharedResources.Stage Q out.sourceOutput.tag (UInt64.ofNat offset) len
            (CurrentCallResourceBodyReadiness.current_room out ready)) ∧
          ∃ base : UInt64,
            SuccessfulTrace.Trace (config options (remaining+1) span) limits
              (Storage.withCurrent #[] (CurrentCallResourceEntry.finishedFrame out) out.finalMachine)
              (Storage.withCurrent #[]
                (CurrentCallResourceSharedStage.afterFrame out frame (by rw [shape.size];decide) base)
                (CurrentCallResourceSharedStage.afterMachine out ready)) := by
  obtain ⟨frame,nextData,nextOwner,Q,shape,pointer,allocation,completion,stage,base,_,_,_,trace⟩:=invoke_with_address out ready nonzero
  exact ⟨frame,nextData,nextOwner,Q,shape,pointer,allocation,completion,stage,base,trace⟩

end
end DuplicatePrefix.CurrentCallResourceSharedInvoke
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceSharedInvoke" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual shared-invoke dependency {dependency}"
