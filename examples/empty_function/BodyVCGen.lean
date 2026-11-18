import empty_function.Specification
import empty_function.LocalUnit
import Miri.Verification.StepWP

/-! Generate the verification program from the production-lowered MIR and
derive scoped safety from its instruction proof. -/
namespace EmptyFunction.BodyVCGen

open Miri.Interpreter Miri.MIR Miri.Verification Miri.Verification.StepWP Std.WP
open EmptyFunction.WholeCall

set_option experimental.vcgen true
set_option autoImplicit false
set_option maxRecDepth 65536

noncomputable def assignment : Instruction :=
  .statement (EmptyFunction.Program.block.statements[0]'(by
    rw [EmptyFunction.Program.one_statement]
    decide)).kind

private theorem assignment_opcode : ∃ destination rhs,
    assignment = .statement (.Assign destination rhs) := by
  exact ⟨_, _, rfl⟩

abbrev hooks (s : Static) := ExecutionMachine.stepHooks s.cfg s.limits
abbrev permitted (_ : State) (_ : Unit) : Prop := True
abbrev ProgramFor (s : Static) := Miri.Verification.StepWP.Program (hooks s) permitted

noncomputable def lower (s : Static) : Option (ProgramFor s) :=
  lowerStraightLine EmptyFunction.Program.root.loaded.body

theorem lowered (s : Static) : lower s =
    some (.seq (.instruction assignment) (.instruction .ret)) := by rfl

theorem matchesAssignment {K U : Type} {older : Array LocalUnit.F} {frame : LocalUnit.F}
    {machine : MachineHooks.MachineState K U}
    (body : frame.body = EmptyFunction.Program.root.loaded.body)
    (pc : frame.location = .mir ⟨0, 0⟩) :
    assignment.matches (LocalUnit.current older frame machine) := by
  simp only [Instruction.matches, LocalUnit.current, Stack.currentFrame?, Array.back?_push, pc, body] <;> rfl

theorem matchesReturn {K U : Type} {older : Array LocalUnit.F} {frame : LocalUnit.F}
    {machine : MachineHooks.MachineState K U}
    (body : frame.body = EmptyFunction.Program.root.loaded.body)
    (pc : frame.location = .mir ⟨0, 1⟩) :
    Instruction.ret.matches (LocalUnit.current older frame machine) := by
  simp only [Instruction.matches, currentTerminator, LocalUnit.current, Stack.currentFrame?,
    Array.back?_push, bind, Bind.bind, Option.bind, pc, body] <;> rfl

abbrev nonUB (error : StepError) (_ : State) : Prop := RunLoop.reportsUB error = false

theorem successfulStep (s : Static) {before after : State} {post : State → Prop}
    (outcome : ExecutionMachine.step s.cfg s.limits () before = (after, .ok true))
    (postcondition : post after) :
    stepPre (hooks s) permitted true post nonUB before := by
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  have stepped : Step.step (hooks s) () before = (after, .ok true) := by
    simpa only [ExecutionMachine.step] using outcome
  simpa only [stepped] using And.intro (rfl : true = true) postcondition

theorem resourceStop (s : Static) {before failed : State} {reason : String}
    (outcome : ExecutionMachine.step s.cfg s.limits () before =
      (failed, .error (.resourceExhaustion reason))) :
    stepPre (hooks s) permitted true (fun _ => False) nonUB before := by
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  have stepped : Step.step (hooks s) () before = (failed, .error (.resourceExhaustion reason)) := by
    simpa only [ExecutionMachine.step] using outcome
  simp only [stepped] <;> rfl

/-- The first instruction can stop with a non-UB error; consequently the
return rule is required only under the first instruction's success condition. -/
theorem verified (s : Static) (depth : Nat) (entry : State) (middle post : State → Prop)
    (atEntry : assignment.matches entry)
    (first : stepPre (hooks s) permitted true middle nonUB entry)
    (next : ∀ state, middle state → Instruction.ret.matches state ∧
      stepPre (hooks s) permitted true
        (fun state => state.stack.frames.size < depth ∧ post state) nonUB state) :
    ∃ program, lower s = some program ∧
      Triple program (fun state => state = entry)
        (fun _ state => state.stack.frames.size < depth ∧ post state) nonUB := by
  have returnRule :
      Triple (Program.instruction (hooks := hooks s) (allowed := permitted) .ret)
        middle (fun _ state => state.stack.frames.size < depth ∧ post state) nonUB := by
    vcgen
    rename_i state ready
    obtain ⟨matched, enabled, execute⟩ := next state ready
    change (currentTerminator state).map Terminator.kind = some .Return at matched
    cases selected : currentTerminator state with
    | none => simp [selected] at matched
    | some term =>
      have kind : term.kind = .Return := by simpa [selected] using matched
      refine ⟨term, rfl, kind, enabled, ?_⟩
      intro choice permitted
      simpa only [step_eq_runTerminator selected (hooks s) choice] using execute choice permitted
  refine ⟨_, lowered s, ?_⟩
  obtain ⟨destination, rhs, opcode⟩ := assignment_opcode
  rw [opcode] at atEntry ⊢
  vcgen
  rename_i beforeState equal
  subst beforeState
  have initial := stepPre_mono (Triple.le_wp returnRule) (fun _ _ h => h) entry first
  refine ⟨atEntry, initial.1, ?_⟩
  intro choice permitted
  simpa only [step_eq_assign atEntry (hooks s) choice] using initial.2 choice permitted

theorem body (s : Static) (depth : Nat) (entry : State) (middle post : State → Prop)
    (inside : depth ≤ entry.stack.frames.size)
    (atEntry : assignment.matches entry)
    (first : stepPre (hooks s) permitted true middle nonUB entry)
    (firstInScope : ∀ state, middle state → depth ≤ state.stack.frames.size)
    (next : ∀ state, middle state → Instruction.ret.matches state ∧
      stepPre (hooks s) permitted true
        (fun state => state.stack.frames.size < depth ∧ post state) nonUB state) :
    FunctionBody.UBFree (ExecutionMachine.step s.cfg s.limits) (fun state => state.stack.frames.size)
      permitted depth entry ∧
    FunctionBody.NormalPost (ExecutionMachine.step s.cfg s.limits)
      (fun state => state.stack.frames.size) permitted depth entry post := by
  obtain ⟨program, selected, triple⟩ := verified s depth entry middle post atEntry first next
  rw [lowered] at selected
  cases selected
  apply twoInstructions_body (hooks := hooks s) (allowed := permitted)
    (first := assignment) (second := .ret) inside
  · intro after choice allowed outcome
    exact firstInScope after (stepPre_outcome first ⟨choice, allowed, outcome⟩).2
  · exact Triple.le_wp triple entry rfl

/-- The resolved call uses the actual frame preparation for this packet. -/
def directCall (s : Static) (p : Packet) : ProgramFor s :=
  .call fun _ before => install s { p with before }

theorem directCall_spec (s : Static) (p : Packet) (entry : State) (post : State → Prop)
    (prepared : install s p = .ok () entry)
    (entryDepth : entry.stack.frames.size = depth p)
    (safe : FunctionBody.UBFree (ExecutionMachine.step s.cfg s.limits)
      (fun state => state.stack.frames.size) permitted (depth p) entry)
    (returned : FunctionBody.NormalPost (ExecutionMachine.step s.cfg s.limits)
      (fun state => state.stack.frames.size) permitted (depth p) entry post) :
    Triple (directCall s p) (fun state => state = p.before) (fun _ => post) nonUB := by
  vcgen [directCall]
  rename_i beforeState equal
  subst beforeState
  change callPre (hooks s) permitted (fun _ before => install s { p with before }) post nonUB p.before
  have same : { p with before := p.before } = p := by cases p; rfl
  apply callPre_of_contract ⟨(), trivial⟩
  · intro choice _ failed error outcome
    rw [same, prepared] at outcome
    cases outcome
  · intro choice _ state outcome
    rw [same, prepared] at outcome
    cases outcome
    exact ⟨entryDepth, safe, returned⟩

theorem returned_of_call (s : Static) (p : Packet) (entry after : State) (post : State → Prop)
    (contract : Triple (directCall s p) (fun state => state = p.before) (fun _ => post) nonUB)
    (prepared : install s p = .ok () entry)
    (reached : FunctionBody.Reachable (ExecutionMachine.step s.cfg s.limits)
      (fun state => state.stack.frames.size) permitted (depth p) entry after)
    (outside : after.stack.frames.size < depth p) : post after := by
  have precondition : callPre (hooks s) permitted (fun _ before => install s { p with before })
      post nonUB p.before := Triple.le_wp contract p.before rfl
  have same : { p with before := p.before } = p := by cases p; rfl
  have checked : entry.stack.frames.size = depth p ∧
      FunctionBody.OnError (Step.step (hooks s)) (fun state => state.stack.frames.size)
        permitted (depth p) entry nonUB ∧
      FunctionBody.NormalPost (Step.step (hooks s))
        (fun state => state.stack.frames.size) permitted (depth p) entry post := by
    simpa only [same, prepared, depth] using precondition.2 () trivial
  delta ExecutionMachine.step at reached
  exact checked.2.2 after reached outside

end EmptyFunction.BodyVCGen
