import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.DuplicatePrefixCallModel
import duplicate_prefix.RootZeroCompletePrefix
import duplicate_prefix.GenericFunctionEntryPrefix

/-! Pure root control after actual entry. Producers retain their own actual
Call.initStackFrame equation; this adapter assumes no ownership frontend. -/
namespace DuplicatePrefix.CurrentCallBodyPrefix
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows
open RootFrameData CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Both pure count branches consume the SAME actual installed frame and
machine. The source immediate remains opaque until the later borrow frontend. -/
theorem body_prefix_of_installed
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (root : RootFrame)
    (raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (value : Immediate Provenance) (count : UInt64) (sourceFrame : FrameState)
    (sourceId : AllocId) (sourceTag : BorTag) (boolId : AllocId) (boolTag : BorTag)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (installed : frame=PositiveRootInstalledFrame.installed root value count sourceFrame sourceId sourceTag boolId boolTag)
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (fuel : Nat) (fuelEq : options.limits.validation=fuel+1) :
    (count=0 → ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span
          (RootZeroCompleteState.tick options remaining span machine))) ∧
      result.body=RootBody.reflected.body.body ∧ result.bodyIdentity=RootBody.reflected.body.identity ∧
      result.functionInstance=RootBody.reflected.functionInstance ∧ result.locals.size=25 ∧
      result.location=.mir ⟨10,0⟩ ∧
      result.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ ∧
      result.returnPlace=frame.returnPlace ∧ result.extra=frame.extra ∧
      result.returnContinuation=frame.returnContinuation ∧ result.vaList=frame.vaList ∧
      CopyHelperCleanup.AllImmediate result) ∧
    (count≠0 → ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span machine)) ∧
      GenericFunctionEntryPrefix.Shape frame result count) := by
  have size : frame.locals.size=25 := by
    rw [installed]
    exact PositiveRootInstalledFrame.size _ _ _ _ _ _ _ _
  have cells (index : Fin 25) := PositiveRootInstalledFrame.slot root raw value count sourceFrame sourceId sourceTag boolId boolTag index
  simp only [←installed] at cells
  obtain ⟨body,identity,callee,_,_,_,clocks,_,location⟩ :=
    PositiveRootInstalledFrame.metadata root value count sourceFrame sourceId sourceTag boolId boolTag
  rw [←installed] at body identity callee clocks location
  have immediate : CopyHelperCleanup.AllImmediate frame := by
    rw [installed]
    exact PositiveRootInstalledFrame.immediate _ raw _ _ _ _ _ _ _
  obtain ⟨current,enabled,mode⟩ := model.defaultTracker
  let source := DuplicatePrefixCallModel.sourceComparator options remaining span machine model
  constructor
  · intro zero
    subst count
    obtain ⟨result,trace,resultBody,resultIdentity,resultCallee,extra,returnPlace,continuation,varargs,_,resultSize,returnLocation,returnValue,all⟩ :=
      RootZeroCompletePrefix.reaches_return options limits remaining span source model.debugOff fuel fuelEq frame machine
        (body.trans root.body) (identity.trans root.identity) (callee.trans root.callee) location size
        (by simpa using congrArg LocalState.value (cells ⟨0,by decide⟩))
        (by simpa using congrArg LocalState.layout (cells ⟨0,by decide⟩))
        (by simpa using congrArg LocalState.value (cells ⟨3,by decide⟩))
        (by simpa using congrArg LocalState.value (cells ⟨4,by decide⟩))
        (by simpa using congrArg LocalState.value (cells ⟨5,by decide⟩))
        (by simpa using congrArg LocalState.layout (cells ⟨4,by decide⟩))
        (by simpa using congrArg LocalState.layout (cells ⟨5,by decide⟩))
        (by simpa using congrArg LocalState.value (cells ⟨2,by decide⟩))
        (by simpa using congrArg LocalState.layout (cells ⟨2,by decide⟩))
        (clocks.trans root.noClocks) immediate current enabled mode model.ghostOff model.shallow
        model.unchecked model.noGc model.fixedScheduler
    exact ⟨result,trace,resultBody.trans (body.trans root.body),resultIdentity.trans (identity.trans root.identity),
      resultCallee.trans (callee.trans root.callee),resultSize,returnLocation,returnValue,returnPlace,extra,continuation,varargs,all⟩
  · intro nonzero
    have unused : ∀ id (valid : id<frame.locals.size),7≤id → id≤12 → frame.locals[id]=⟨.dead,none⟩ := by
      intro id valid lower upper
      have row := cells ⟨id,by omega⟩
      simp only [show ¬(14=id ∨ 13=id ∨ 6=id ∨ 0=id) by omega,show ¬2=id by omega,
        show ¬1=id by omega,ite_false] at row
      exact row
    exact GenericFunctionEntryPrefix.executes_preserving options limits remaining span source model.debugOff fuel fuelEq
      frame machine count nonzero size
      (by simpa using congrArg LocalState.value (cells ⟨2,by decide⟩))
      (by simpa using congrArg LocalState.layout (cells ⟨2,by decide⟩))
      (by simpa using congrArg LocalState.value (cells ⟨3,by decide⟩))
      (by simpa using congrArg LocalState.layout (cells ⟨3,by decide⟩))
      (by simpa using congrArg LocalState.value (cells ⟨4,by decide⟩))
      (by simpa using congrArg LocalState.value (cells ⟨5,by decide⟩))
      (by simpa using congrArg LocalState.layout (cells ⟨4,by decide⟩))
      (by simpa using congrArg LocalState.layout (cells ⟨5,by decide⟩)) unused
      (body.trans root.body) (identity.trans root.identity) (callee.trans root.callee) location
      (clocks.trans root.noClocks) immediate current enabled mode model.ghostOff model.shallow
      model.unchecked model.noGc model.fixedScheduler
end
end DuplicatePrefix.CurrentCallBodyPrefix

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallBodyPrefix" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generic after-entry body-prefix dependency {dependency}"
