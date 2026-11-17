import duplicate_prefix.CurrentCallPostEntryCheckpoint
import duplicate_prefix.RootZeroCompletePrefix

namespace DuplicatePrefix.CurrentCallCheckpointZeroControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CurrentCallPostEntryCheckpoint
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

private theorem cell {frame : CompilerFrameContext.ActualFrame} {index : Nat}
    {value : LocalState Provenance LocalLayout} (valid : index<frame.locals.size)
    (found : frame.locals[index]?=some value) : frame.locals[index]'valid=value :=
  Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans found)

/-- The zero-count execution uses the same installed checkpoint and existing
root branch proof. It requires no shared or Len operation. -/
theorem invoke {options remaining span len place}
    (checkpoint : Checkpoint options remaining span len 0 place) (limits : ExecutionMachine.Limits) :
    ∃ frame : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] checkpoint.frame checkpoint.machine)
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span
          (RootZeroCompleteState.tick options remaining span checkpoint.machine))) ∧
      frame.body=checkpoint.frame.body ∧frame.bodyIdentity=checkpoint.frame.bodyIdentity ∧frame.functionInstance=checkpoint.frame.functionInstance ∧
      frame.extra=checkpoint.frame.extra ∧frame.returnPlace=checkpoint.frame.returnPlace ∧frame.returnContinuation=checkpoint.frame.returnContinuation ∧
      frame.vaList=checkpoint.frame.vaList ∧frame.localsIdentity=checkpoint.frame.localsIdentity ∧frame.locals.size=25 ∧
      frame.location=.mir ⟨10,0⟩ ∧frame.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ ∧
      CopyHelperCleanup.AllImmediate frame:=by
  have valid (i : Fin 25) : i.val<checkpoint.frame.locals.size:=by rw [checkpoint.size];exact i.isLt
  have zero : checkpoint.frame.locals[0]'(valid ⟨0,by decide⟩)=⟨.live (.immediate .uninit),none⟩:=by
    apply cell
    simpa using checkpoint.slots ⟨0,by decide⟩
  have second:=cell (valid ⟨2,by decide⟩) checkpoint.countLocal
  have dead (i : Fin 25) (first : 3≤i.val) (last : i.val<6) : checkpoint.frame.locals[i.val]'(valid i)=⟨.dead,none⟩:=by
    apply cell
    simpa only [show ¬(14=i.val ∨13=i.val ∨6=i.val ∨0=i.val) by omega,
      show ¬2=i.val by omega,show ¬1=i.val by omega,ite_false] using checkpoint.slots i
  exact RootZeroCompletePrefix.reaches_return options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span checkpoint.machine checkpoint.model)
    checkpoint.model.debugOff checkpoint.validationFuel checkpoint.validationEq checkpoint.frame checkpoint.machine
    checkpoint.body checkpoint.identity checkpoint.callee checkpoint.location checkpoint.size
    (congrArg LocalState.value zero) (congrArg LocalState.layout zero)
    (congrArg LocalState.value (dead ⟨3,by decide⟩ (by decide) (by decide)))
    (congrArg LocalState.value (dead ⟨4,by decide⟩ (by decide) (by decide)))
    (congrArg LocalState.value (dead ⟨5,by decide⟩ (by decide) (by decide)))
    (congrArg LocalState.layout (dead ⟨4,by decide⟩ (by decide) (by decide)))
    (congrArg LocalState.layout (dead ⟨5,by decide⟩ (by decide) (by decide)))
    (congrArg LocalState.value second) (congrArg LocalState.layout second) checkpoint.noClocks checkpoint.immediate
    checkpoint.tracker checkpoint.tracked checkpoint.mode checkpoint.model.ghostOff checkpoint.model.shallow
    checkpoint.model.unchecked checkpoint.model.noGc checkpoint.model.fixedScheduler

end
end DuplicatePrefix.CurrentCallCheckpointZeroControl
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointZeroControl" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common zero control dependency {dependency}"
