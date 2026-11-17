import duplicate_prefix.CopyLanguageGuard
import duplicate_prefix.CopyHelperFacts
import duplicate_prefix.RootScalarQueries
import duplicate_prefix.PtrMetadataReturn
namespace DuplicatePrefix.CopyHelperControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem false_switch_step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (location : frame.location = .mir ⟨1,0⟩)
    (valid : (5 : MIR.LocalId) < frame.locals.size)
    (live : frame.locals[5].value = .live (.immediate (.scalar (.fromBool false))))
    (cached : frame.locals[5].layout = some RootCompilerFacts.boolLayout)
    (noClocks : frame.extra.dataRace = none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghost : machine.user.payload.ghost = false) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ExecutionMachine.step config limits () (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames {frame with location := .mir ⟨6,0⟩}
        (PtrMetadataReturn.accountedMachine options remaining span machine),.ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let before := Storage.withCurrent frames frame machine
  let next := PtrMetadataReturn.accountedMachine options remaining span machine
  let afterAccount := Storage.withCurrent frames frame next
  let block := HelperCompilerFacts.copyBody.body.basicBlocks[1]'(by decide +kernel)
  have blockAt : frame.body.basicBlocks[1]? = some block := by rw [sourceBody];simp [block]
  have kind : block.terminator.kind = .SwitchInt (.Move ⟨5,#[]⟩) ⟨#[.Case 0 6],2⟩ := by decide +kernel
  have noStatement : block.statements[0]? = none := by decide +kernel
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have nextGhost : next.user.payload.ghost = false := by rw [PtrMetadataReturn.accounted_ghost];exact ghost
  have getter : (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)).compiler.validationInProgress
      afterAccount = .ok false afterAccount := by
    change config.compiler.validationInProgress afterAccount = _
    rw [fields.compilerValidationInProgress]
    simp [ValidityMachine.validationInProgress,afterAccount,Storage.withCurrent,nextGhost,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  have boolInit : CopyCompilerFacts.initializedScalar RootCompilerFacts.boolLayout = true := by decide +kernel
  have readable := CopyCompilerFacts.initialized_scalar_exists RootCompilerFacts.boolLayout boolInit
  have switch := CopyLanguageGuard.canonical_false_local_switch options limits (remaining+1) span debugOff
    frames frame next 5 6 2 block.terminator valid live cached (by decide +kernel) readable noClocks getter kind
    (RootScalarQueries.bool_classification options (remaining+1) span limits)
    (RootScalarQueries.bool_layout options (remaining+1) span limits) (by decide +kernel)
  have effect : (ExecutionMachine.stepHooks config limits).terminator () block.terminator afterAccount =
      (Storage.withCurrent frames {frame with location := .mir ⟨6,0⟩} next,.ok ()) := by
    rw [switch]
    exact GenericCallReturn.goto_current frames frame next 6
  have accounting := SourceControl.before_terminator config limits () before
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  exact StepFacts.step_terminator (ExecutionMachine.stepHooks config limits) () before afterAccount _ frame
    ⟨1,0⟩ block (by simp [before,Storage.withCurrent,Stack.currentFrame?]) location blockAt noStatement accounting effect

theorem unit_goto_step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (location : frame.location = .mir ⟨6,1⟩)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ExecutionMachine.step config limits () (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames {frame with location := .mir ⟨7,0⟩}
        (PtrMetadataReturn.accountedMachine options remaining span machine),.ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := HelperCompilerFacts.copyBody.body.basicBlocks[6]'(by decide +kernel)
  exact SourceControl.goto_step config limits () frames frame machine ⟨6,1⟩ block 7 location
    (by rw [sourceBody];simp [block]) (by decide +kernel) (by exact ⟨#[],by decide +kernel⟩)
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed

#print axioms false_switch_step
open Lean Elab Command in
run_cmd do
  for declaration in [``false_switch_step, ``unit_goto_step] do
   for dependency in (← collectAxioms declaration) do
     unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
       throwError "unapproved axiom {dependency}"
end DuplicatePrefix.CopyHelperControl
