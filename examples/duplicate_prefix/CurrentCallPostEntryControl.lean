import duplicate_prefix.CurrentCallPostEntryCheckpoint
import duplicate_prefix.GenericFunctionEntryPrefix

namespace DuplicatePrefix.CurrentCallPostEntryControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CandidateCurrentJointCall CurrentCallPostEntryCheckpoint
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

private theorem cell {frame : CompilerFrameContext.ActualFrame} {index : Nat}
    {value : LocalState Provenance LocalLayout} (valid : index<frame.locals.size)
    (found : frame.locals[index]?=some value) : frame.locals[index]'valid=value := by
  exact Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans found)

/-- The common nonzero guard prefix starts at the actual installed frame.
It neither repeats call initialization nor depends on a uniform completion. -/
theorem before_shared {options remaining span len count place}
    (checkpoint : Checkpoint options remaining span len count place)
    (limits : ExecutionMachine.Limits) (nonzero : count≠0) :
    ∃ frame : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] checkpoint.frame checkpoint.machine)
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span checkpoint.machine)) ∧
      GenericFunctionEntryPrefix.Shape checkpoint.frame frame count := by
  have valid (i : Fin 25) : i.val<checkpoint.frame.locals.size := by rw [checkpoint.size];exact i.isLt
  have second:=cell (valid ⟨2,by decide⟩) checkpoint.countLocal
  have dead (i : Fin 25) (three : 3≤i.val) (six : i.val<6) :
      checkpoint.frame.locals[i.val]'(valid i)=⟨.dead,none⟩ := by
    apply cell
    simpa only [show ¬(14=i.val ∨13=i.val ∨6=i.val ∨0=i.val) by omega,
      show ¬2=i.val by omega,show ¬1=i.val by omega,ite_false] using checkpoint.slots i
  have unused : ∀ i (bound : i<checkpoint.frame.locals.size),7≤i →i≤12 →
      checkpoint.frame.locals[i]'bound=⟨.dead,none⟩ := by
    intro i bound first last
    apply cell
    have small : i<25:=by rw [checkpoint.size] at bound;exact bound
    simpa only [show ¬(14=i ∨13=i ∨6=i ∨0=i) by omega,
      show ¬2=i by omega,show ¬1=i by omega,ite_false] using checkpoint.slots ⟨i,small⟩
  exact GenericFunctionEntryPrefix.executes_preserving options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span checkpoint.machine checkpoint.model)
    checkpoint.model.debugOff checkpoint.validationFuel checkpoint.validationEq checkpoint.frame checkpoint.machine count nonzero
    checkpoint.size (congrArg LocalState.value second) (congrArg LocalState.layout second)
    (congrArg LocalState.value (dead ⟨3,by decide⟩ (by decide) (by decide)))
    (congrArg LocalState.layout (dead ⟨3,by decide⟩ (by decide) (by decide)))
    (congrArg LocalState.value (dead ⟨4,by decide⟩ (by decide) (by decide)))
    (congrArg LocalState.value (dead ⟨5,by decide⟩ (by decide) (by decide)))
    (congrArg LocalState.layout (dead ⟨4,by decide⟩ (by decide) (by decide)))
    (congrArg LocalState.layout (dead ⟨5,by decide⟩ (by decide) (by decide)))
    unused checkpoint.body checkpoint.identity checkpoint.callee checkpoint.location checkpoint.noClocks checkpoint.immediate
    checkpoint.tracker checkpoint.tracked checkpoint.mode checkpoint.model.ghostOff checkpoint.model.shallow
    checkpoint.model.unchecked checkpoint.model.noGc checkpoint.model.fixedScheduler

end
end DuplicatePrefix.CurrentCallPostEntryControl

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallPostEntryControl" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common post-entry control dependency {dependency}"
