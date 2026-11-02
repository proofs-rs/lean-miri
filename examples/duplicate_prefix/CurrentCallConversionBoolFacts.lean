import duplicate_prefix.CurrentCallConversionBoolPhase

/-! Current machine metadata after the actual converter and Bool protection.
This frame is shared by the positive entry cases. -/
namespace DuplicatePrefix.CurrentCallConversionBoolFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CurrentCallResourceNormalization CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

variable {options : EvalConfigurationCore.Options} {remaining modelRemaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    {machine : Before} {tracker : MachineHooks.BorrowState}
    {frames : Array CompilerFrameContext.ActualFrame} {frame : CompilerFrameContext.ActualFrame}
    {borrowFrame : FrameState} {place : MPlaceTy Provenance}
    (D : CurrentCallConversionBoolPhase.CurrentData machine tracker frames frame borrowFrame place)
    (externStatic : Miri.MIR.DefId → MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance))
    (tail : List AllocId) (charge reserve : Nat) (finalAddresses : Miri.Memory.AllocAddresses.GlobalAddressState)
    (finalTape : ExecutionChoices.Tape)
    (result : CurrentCallConversionFiniteFold.Result D.source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic D.registered.machine D.next
      tail charge reserve finalAddresses finalTape)
    (outcome : CurrentCallConversionBoolPhase.Protected (options := options) (remaining := remaining) (span := span)
      D externStatic tail charge reserve finalAddresses finalTape result)

include result outcome in
theorem threads : outcome.post.machine.threads = machine.threads := by
  rw [outcome.machineEq, result.frame, CurrentCallConversionFiniteFold.state_eq]
  rfl

include result outcome in
theorem model (beforeModel : DuplicatePrefixCallModel.Model options modelRemaining span machine)
    (defaultMode : tracker.retagMode = .Default) :
    DuplicatePrefixCallModel.Model options modelRemaining span outcome.post.machine := by
  have controlEq : (config options (modelRemaining + 1) span).terminators.getControl outcome.post.machine.user =
      (config options (modelRemaining + 1) span).terminators.getControl machine.user := by
    rw [outcome.machineEq, result.frame, CurrentCallConversionFiniteFold.state_eq]
    rw [(CanonicalConfigFacts.actual_fields options () (modelRemaining + 1) span).terminators]
    rfl
  refine ⟨beforeModel.debugOff, beforeModel.preciseOff, beforeModel.implicitOff, ?_, ?_,
    ⟨_, outcome.tracked, defaultMode⟩, ?_, ?_, ?_, ?_, ?_, ?_, beforeModel.nullComparator, beforeModel.sourceMatches⟩
  · rw [outcome.machineEq, result.frame, CurrentCallConversionFiniteFold.state_eq]
    exact beforeModel.ghostOff
  · rw [outcome.machineEq, result.frame, CurrentCallConversionFiniteFold.state_eq]
    exact beforeModel.shallow
  · rw [outcome.machineEq, result.frame, CurrentCallConversionFiniteFold.state_eq]
    exact beforeModel.noDataRace
  · rw [outcome.machineEq, result.frame, CurrentCallConversionFiniteFold.state_eq]
    exact beforeModel.noBackend
  · rw [outcome.machineEq, result.frame, CurrentCallConversionFiniteFold.state_eq]
    exact beforeModel.metadata
  · rw [threads D externStatic tail charge reserve finalAddresses finalTape result outcome]
    exact beforeModel.fixedScheduler
  · change ((config options (modelRemaining + 1) span).terminators.getControl outcome.post.machine.user).checkedArithmetic = false
    rw [controlEq]
    exact beforeModel.unchecked
  · change ((config options (modelRemaining + 1) span).terminators.getControl outcome.post.machine.user).gcInterval = 0
    rw [controlEq]
    exact beforeModel.noGc

include result outcome in
theorem origins (beforeOrigins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types) :
    DuplicatePrefixTypeCacheOrigins.Origins outcome.post.machine.user.payload.payload.user.types := by
  rw [outcome.machineEq, result.frame, CurrentCallConversionFiniteFold.state_eq]
  exact beforeOrigins

private theorem replace_twice {α : Type} (rows : Array (AllocId × α)) (id : AllocId) (first second : α) :
    ((((rows.filter (fun row => row.1 != id)).push (id, first)).filter (fun row => row.1 != id)).push (id, second)) =
      (rows.filter (fun row => row.1 != id)).push (id, second) := by
  simp [Array.filter_filter]

include result outcome in
theorem addresses : outcome.post.machine.user.addresses = result.addresses := by
  rw [outcome.machineEq, result.frame, CurrentCallConversionFiniteFold.state_eq]
  rfl

include result outcome in
theorem live : outcome.post.machine.memory.live =
    (machine.memory.live.filter (fun row => row.1 != D.family.allocation)).push
      (D.family.allocation, ⟨.machine .global, outcome.output.window.allocation⟩) := by
  have registeredMemory : D.registered.machine.memory = machine.memory := rfl
  have actual := congrArg (fun state : Before => state.memory.live) outcome.machineEq
  rw [result.frame, CurrentCallConversionFiniteFold.state_eq] at actual
  simpa only [CurrentCallConversionSourceCopy.childMachine, CurrentCallConversionSourceCopy.rootMachine,
    CurrentCallConversionMaterialize.installed, RetagEntry.updatedMemory, MemoryExtras.putAllocation, replace_twice, registeredMemory] using actual

include result outcome in
theorem extras : outcome.post.machine.user.payload.payload.user.runtime.extras.allocations =
    (machine.user.payload.payload.user.runtime.extras.allocations.filter (fun row => row.1 != D.family.allocation)).push
      (D.family.allocation, ⟨none, #[]⟩) := by
  rw [outcome.machineEq, result.frame, CurrentCallConversionFiniteFold.state_eq]
  rfl

end
end DuplicatePrefix.CurrentCallConversionBoolFacts

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallConversionBoolFacts.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved Bool metadata frame dependency {name}: {dependency}"
