import duplicate_prefix.CopyHelperSteps
import duplicate_prefix.CopyHelperControl
namespace DuplicatePrefix.CopyHelperUnitBlock
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem actual_two_steps
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (old : Immediate Provenance)
    (valid : 4 < frame.locals.size)
    (live : frame.locals[4].value = .live (.immediate old))
    (uncached : frame.locals[4].layout = none)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (location : frame.location = .mir ⟨6,0⟩)
    (fnInstance : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let written := CopyHelperSteps.advance (ActualLocalCopy.written frame 4 CopyHelperUnit.layout valid .uninit) ⟨6,0⟩
    let done := {written with location := .mir ⟨7,0⟩}
    ExecutionMachine.step config limits () (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore written machine,.ok true) ∧
    ExecutionMachine.step config limits () (Storage.withCurrent framesBefore written machine) =
      (Storage.withCurrent framesBefore done (PtrMetadataReturn.accountedMachine options remaining span machine),.ok true) := by
  constructor
  · exact CopyHelperSteps.unit_assignment_step options limits remaining span source debugOff fuel validationFuel
      framesBefore frame machine old valid live uncached sourceBody identity location fnInstance noClocks
      tracker tracked defaultMode ghostFalse shallow
  · apply CopyHelperControl.unit_goto_step options limits remaining span framesBefore _ machine
    · exact sourceBody
    · rfl
    · exact unchecked
    · exact noGc
    · exact fixed

#print axioms actual_two_steps
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``actual_two_steps) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved axiom {dependency}"
end DuplicatePrefix.CopyHelperUnitBlock
