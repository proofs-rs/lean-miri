import empty_function.BodyFailures

namespace EmptyFunction.BodyTotal
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A successfully built canonical runner has positive callback capacity.
This follows from its actual construction result, without a resource margin. -/
theorem capacity_positive (s : Static) : 0 < s.capacity := by
  by_cases zeroCapacity : s.capacity = 0
  · have zero : Configuration.rootConfig s.prepared s.bytes s.options () 0 =
        .error (.resourceExhaustion "execution callback construction capacity") := by
      unfold Configuration.rootConfig
      rw [EvalConfigurationCore.make_eq_context,EvalConfigurationCore.makeWithForeignContext]
      rfl
    have built := s.built
    rw [zeroCapacity,zero] at built
    cases built
  · omega

/-- The actual exported assignment either advances to Return or stops with a
classified resource error. This statement has no fuel/headroom premise. -/
theorem step (s : Static) (metadata : Metadata s) (profile : Profile s)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (bodyIdentity : frame.bodyIdentity = s.loaded.identity)
    (body : frame.body = s.loaded.body)
    (function : frame.functionInstance = s.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ExecutionMachine.step s.cfg s.limits ()
        (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      (BodyStep.current frames {(BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) with
        location := .mir ⟨0,1⟩} machine,.ok true) ∨
    ∃ reason, ExecutionMachine.step s.cfg s.limits ()
        (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine,
        .error (.resourceExhaustion reason)) := by
  have positive := capacity_positive s
  by_cases one : s.capacity = 1
  · exact Or.inr ⟨_,BodyFailures.step_capacity_one s metadata profile one frames frame machine
      bodyIdentity body function location noClocks noGhost shallow⟩
  · have capacity : s.capacity = (s.capacity-2)+2 := by omega
    by_cases zero : s.options.limits.validation = 0
    · exact Or.inr ⟨_,BodyFailures.step_validation_zero s metadata profile (s.capacity-2) capacity zero
        frames frame machine bodyIdentity body function location noClocks noGhost shallow⟩
    · exact Or.inl (BodyAssignment.step s metadata profile (s.capacity-2) capacity (by omega)
        frames frame machine bodyIdentity body function location noClocks noGhost shallow)

theorem of_success (s : Static) (metadata : Metadata s) (profile : Profile s)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (bodyIdentity : frame.bodyIdentity = s.loaded.identity)
    (body : frame.body = s.loaded.body)
    (function : frame.functionInstance = s.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (after : State)
    (actual : ExecutionMachine.step s.cfg s.limits ()
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) = (after,.ok true)) :
    ∃ remaining, s.capacity = remaining+2 ∧ 0 < s.options.limits.validation ∧
      after = BodyStep.current frames {(BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) with
        location := .mir ⟨0,1⟩} machine := by
  have positive := capacity_positive s
  have notOne : s.capacity ≠ 1 := by
    intro one
    have failure := BodyFailures.step_capacity_one s metadata profile one frames frame machine
      bodyIdentity body function location noClocks noGhost shallow
    rw [actual] at failure
    cases failure
  have capacity : s.capacity = (s.capacity-2)+2 := by omega
  have validation : 0 < s.options.limits.validation := by
    by_cases zero : s.options.limits.validation = 0
    · have failure := BodyFailures.step_validation_zero s metadata profile (s.capacity-2) capacity zero
        frames frame machine bodyIdentity body function location noClocks noGhost shallow
      rw [actual] at failure
      cases failure
    · omega
  have exactStep := BodyAssignment.step s metadata profile (s.capacity-2) capacity validation
    frames frame machine bodyIdentity body function location noClocks noGhost shallow
  rw [actual] at exactStep
  exact ⟨s.capacity-2,capacity,validation,congrArg Prod.fst exactStep⟩

open Lean Elab Command in
run_cmd do
  for name in #[``capacity_positive,``step,``of_success] do
    for dependency in (← collectAxioms name) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved total body axiom {dependency} in {name}"
#print axioms step
end EmptyFunction.BodyTotal
