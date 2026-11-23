import duplicate_prefix.RootZeroCompleteSwitch
import duplicate_prefix.SuccessfulTrace
import Miri.Verification.EffectSpecs

/-! VC generation over the first branch of the actual imported
`duplicate_prefix` MIR from PR #12, revision
7950c01b18013969c360df535b8b888dd6181dff. The symbolic memory and
frame conditions are those of the source-derived switch proof. -/
namespace DuplicatePrefix.VCGen

open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.Verification Miri.Verification.StepWP Std.WP

set_option experimental.vcgen true
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option autoImplicit false

private theorem unit_transition {P L E M : Type} {before after : StepState P L E M}
    {run : Unit → StepResult (StepState P L E M) Bool} {more : Bool}
    {post : StepState P L E M → Prop} {onError : StepError → StepState P L E M → Prop}
    (outcome : run () = (after, .ok more)) (returned : post after) :
    transitionPre (fun _ _ => True) more run post onError before := by
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  rw [outcome]
  exact ⟨rfl, returned⟩

/-- Use the actual zero-test terminator and its source-derived transition
proof. Both successor blocks are handled for every count. -/
theorem zero_test
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (count : UInt64)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨0, 5⟩)
    (size : frame.locals.size = 25)
    (valid : (4 : MIR.LocalId) < frame.locals.size)
    (live : (frame.locals[4]'valid).value = .live (.immediate (.scalar (.fromBool (count == 0)))))
    (cached : (frame.locals[4]'valid).layout = some RootCompilerFacts.boolLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (unchecked :
      ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
        machine.user).checkedArithmetic = false)
    (noGc :
      ((PreparedContracts.actualConfig options () (remaining + 1) span).terminators.getControl
        machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining + 1) span
    let before := Storage.withCurrent frames frame machine
    let target := if count == 0 then 1 else 2
    Triple (Program.instruction (hooks := ExecutionMachine.stepHooks config limits)
      (allowed := fun _ _ => True)
      (.terminator (.SwitchInt (.Move ⟨4, #[]⟩) ⟨#[.Case 0 2], 1⟩))) (· = before)
      (fun _ after =>
        after = Storage.withCurrent frames {frame with location := .mir ⟨target, 0⟩}
          (SourceControl.accounted config.terminators before).machine)
      (fun _ _ => False) := by
  dsimp only
  vcgen
  rename_i state atEntry
  subst state
  let block := RootBody.reflected.body.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[0]? = some block := by
    rw [body]
    exact Array.getElem?_eq_getElem _
  have noStatement : block.statements[5]? = none := by with_unfolding_all rfl
  have selected : currentTerminator (Storage.withCurrent frames frame machine) =
      some block.terminator := by
    simp [currentTerminator, Storage.withCurrent, Stack.currentFrame?, location, blockAt,
      noStatement, bind, Bind.bind, Option.bind]
  have kind : block.terminator.kind = .SwitchInt (.Move ⟨4, #[]⟩) ⟨#[.Case 0 2], 1⟩ := by
    with_unfolding_all rfl
  refine ⟨block.terminator, selected, kind, ?_⟩
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  have actual := RootZeroCompleteSwitch.switch_exact options limits
    remaining span debugOff frames frame machine count body identity callee location size valid
    live cached noClocks ghost unchecked noGc fixed
  dsimp only at actual
  delta ExecutionMachine.step at actual
  have effect := (step_eq_runTerminator selected (ExecutionMachine.stepHooks config limits) ()).symm.trans actual
  exact unit_transition effect rfl

/-- A successful root trace proves safety for all reachable prefixes and fixes
the resulting state on scope exit. Unit is the actual choice type of the
existing duplicate_prefix client. -/
theorem contracts_of_trace {K U O X Host : Type} [DecidableEq K]
    {cfg : ExecutionMachine.Config K U Unit O X Host} {limits : ExecutionMachine.Limits}
    {entry final : MachineHooks.State K U}
    (trace : SuccessfulTrace.Trace cfg limits entry final)
    (finished : final.stack.frames = #[]) :
    FunctionBody.UBFree (ExecutionMachine.step cfg limits) (·.stack.frames.size)
      (fun _ _ => True) 1 entry ∧
    FunctionBody.NormalPost (ExecutionMachine.step cfg limits) (·.stack.frames.size)
      (fun _ _ => True) 1 entry (· = final) := by
  have outside : CallSafety.pastCallBoundary 1 final := by
    simp [CallSafety.pastCallBoundary, CallSafety.frameDepth, finished]
  apply FunctionBody.ofInvariant (fun state => SuccessfulTrace.Trace cfg limits state final) trace
  · rintro before after ⟨⟩ suffix inside _ outcome
    obtain ⟨_, expected, tail⟩ := SuccessfulTrace.active_head 1 suffix inside outside
    rw [expected] at outcome
    cases outcome
    exact tail
  · rintro before after ⟨⟩ error suffix inside _ outcome
    obtain ⟨_, expected, _⟩ := SuccessfulTrace.active_head 1 suffix inside outside
    rw [expected] at outcome
    simp at outcome
  · intro after suffix outside
    cases suffix with
    | refl => rfl
    | next step _ =>
      have empty : after.stack.frames = #[] := Array.size_eq_zero_iff.mp (by omega)
      have stopped : ExecutionMachine.step cfg limits () after = (after, .ok false) := by
        simp [ExecutionMachine.step, Step.step, Stack.currentFrame?, empty, Id.run, pure, Pure.pure]
      rw [stopped] at step
      simp at step

/-- The exact number of continuing driver steps, followed by an empty-stack
check. These are real steps of the same interpreter used by the call contract. -/
def rootProgram {K U O X Host : Type} [DecidableEq K]
    (cfg : ExecutionMachine.Config K U Unit O X Host) (limits : ExecutionMachine.Limits) :
    Nat → Program (ExecutionMachine.stepHooks cfg limits) (fun _ _ => True)
  | 0 => .step false
  | count + 1 => .seq (.step true) (rootProgram cfg limits count)

theorem program_of_trace {K U O X Host : Type} [DecidableEq K]
    {cfg : ExecutionMachine.Config K U Unit O X Host} {limits : ExecutionMachine.Limits}
    {entry final : MachineHooks.State K U}
    (trace : SuccessfulTrace.Trace cfg limits entry final)
    (stopped : ExecutionMachine.step cfg limits () final = (final, .ok false)) :
    ∃ count, Triple (rootProgram cfg limits count) (· = entry) (fun _ => (· = final))
      (fun _ _ => False) := by
  induction trace with
  | refl state =>
    refine ⟨0, ?_⟩
    vcgen [rootProgram]
    rename_i current atEntry
    subst current
    apply (stepPre_iff_driverPre _ _ _ _ _ state).mp
    refine ⟨⟨(), trivial⟩, ?_⟩
    rintro ⟨⟩ _
    dsimp only
    rw [show Step.step (ExecutionMachine.stepHooks cfg limits) () state = _ from stopped]
    exact ⟨rfl, rfl⟩
  | @next before after done head _ ih =>
    obtain ⟨count, tail⟩ := ih stopped
    refine ⟨count + 1, ?_⟩
    suffices checked : Triple (Program.step (hooks := ExecutionMachine.stepHooks cfg limits)
        (allowed := fun _ _ => True) true) (· = before)
        (fun _ => pre (rootProgram cfg limits count) (· = done) (fun _ _ => False))
        (fun _ _ => False) by
      apply Triple.iff.mpr
      intro state equal
      have outcome := Triple.le_wp checked state equal
      exact outcome
    vcgen
    rename_i current atEntry
    subst current
    apply (stepPre_iff_driverPre _ _ _ _ _ before).mp
    refine ⟨⟨(), trivial⟩, ?_⟩
    rintro ⟨⟩ _
    dsimp only
    rw [show Step.step (ExecutionMachine.stepHooks cfg limits) () before = _ from head]
    exact ⟨rfl, Triple.le_wp tail after rfl⟩

/-- Discharge the generated call VC with actual setup and the body's contracts. -/
theorem prepared_root_call {K U O X Host : Type} [DecidableEq K]
    {cfg : ExecutionMachine.Config K U Unit O X Host} {limits : ExecutionMachine.Limits}
    {before entry final : MachineHooks.State K U}
    (prepare : Unit → MachineHooks.State K U →
      EStateM.Result StepError (MachineHooks.State K U) Unit)
    (emptyCaller : before.stack.frames = #[]) (entryDepth : entry.stack.frames.size = 1)
    (initialized : prepare () before = .ok () entry)
    (trace : SuccessfulTrace.Trace cfg limits entry final) (finished : final.stack.frames = #[]) :
    Triple (Program.call (hooks := ExecutionMachine.stepHooks cfg limits) (allowed := fun _ _ => True)
      prepare) (· = before) (fun _ after => after = final)
      (fun error _ => RunLoop.reportsUB error = false) := by
  vcgen
  rename_i state atEntry
  subst state
  obtain ⟨safe, returned⟩ := contracts_of_trace trace finished
  apply callPre_of_contract ⟨(), trivial⟩
  · rintro ⟨⟩ _ failed error outcome
    rw [initialized] at outcome
    cases outcome
  · rintro ⟨⟩ _ newEntry outcome
    rw [initialized] at outcome
    cases outcome
    simpa only [emptyCaller, Array.size_empty, Nat.zero_add] using ⟨entryDepth, safe, returned⟩

end DuplicatePrefix.VCGen
