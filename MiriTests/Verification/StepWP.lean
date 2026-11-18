import Miri.Verification.StepWP
import MiriTests.ControlFlow.Transitions

/-! The control-flow fixture runs the original Step driver and ControlFlow
implementation with fixture callbacks. -/
namespace MiriTests.Verification.StepWP

open Miri.Interpreter Miri.Verification.StepWP Std.WP
open Lean.Order

set_option experimental.vcgen true

private abbrev DriverProgram := Program ControlTests.stepHooks (fun _ _ => True)

private def advance : DriverProgram :=
  .step true

private def stopCheck : DriverProgram :=
  checkEmptyStack ControlTests.stepHooks (fun _ _ => True)

private def noError : StepError → ControlTests.S → Prop := fun _ _ => False

private def entry : ControlTests.S := ControlTests.program ControlTests.fixture

private def afterGoto : ControlTests.S :=
  (Step.step ControlTests.stepHooks () entry).1

private def afterNop : ControlTests.S :=
  (Step.step ControlTests.stepHooks () afterGoto).1

private def afterReturn : ControlTests.S :=
  (Step.step ControlTests.stepHooks () afterNop).1

private def finalPost (_ : Unit) (state : ControlTests.S) : Prop :=
  state.stack.frames.isEmpty = true ∧ state.machine = [9, 9, 1, 2, 3, 4]

/-- The three successful driver iterations are Goto, Nop and Return.
The final iteration checks that the return emptied the stack. -/
theorem gotoNopReturn :
    Triple (Program.seq advance (Program.seq advance (Program.seq advance stopCheck)))
      (fun state => state = entry)
      finalPost noError := by
  vcgen [advance, stopCheck]
  subst_vars
  change stepPre ControlTests.stepHooks (fun _ _ => True) true
    (wp (Program.seq advance (Program.seq advance stopCheck)) finalPost noError) noError entry
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  change true = true ∧
    wp (Program.seq advance (Program.seq advance stopCheck)) finalPost noError afterGoto
  refine ⟨rfl, ⟨⟨(), trivial⟩, ?_⟩⟩
  rintro ⟨⟩ _
  change true = true ∧ wp (Program.seq advance stopCheck) finalPost noError afterNop
  refine ⟨rfl, ⟨⟨(), trivial⟩, ?_⟩⟩
  rintro ⟨⟩ _
  change true = true ∧ wp stopCheck finalPost noError afterReturn
  refine ⟨rfl, ⟨⟨(), trivial⟩, ?_⟩⟩
  rintro ⟨⟩ _
  exact ⟨rfl, rfl, rfl⟩

example :
    Triple (Program.instruction (hooks := ControlTests.stepHooks) (allowed := fun _ _ => True)
      (.goto 1 #[])) (· = entry)
      (fun _ after => after.stack.currentFrame?.map (·.location) = some (.mir ⟨1, 0⟩) ∧
        after.machine = [9]) noError := by
  vcgen
  subst_vars
  refine ⟨_, rfl, rfl, ⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  exact ⟨rfl, rfl, rfl⟩

/-- A symbolic proof can use a registered rule without unfolding the driver. -/
example (state : ControlTests.S) :
    Triple (checkEmptyStack ControlTests.stepHooks (fun _ _ => True))
      (fun before => before = state ∧ before.stack.currentFrame? = none)
      (fun _ after => after = state) noError := by
  vcgen
  rename_i before h
  exact ⟨h.2, ⟨(), trivial⟩, h.1⟩

/-- An empty set of permitted choices fails even with trivial postconditions. -/
example : ¬ stepPre ControlTests.stepHooks (fun _ _ => False) true
    (fun _ => True) (fun _ _ => True) entry := by
  rintro ⟨⟨_, permitted⟩, _⟩
  exact permitted

private def unsupportedHooks := { ControlTests.stepHooks with
  beforeTerminator := fun _ state => (ControlTests.log 99 state, .error (.unsupported "fixture")) }

/-- Errors preserve the state produced by the failing callback. -/
example : stepPre unsupportedHooks (fun _ _ => True) true (fun _ => False)
    (fun error state => error = .unsupported "fixture" ∧ state.machine = [99]) entry := by
  exact ⟨⟨(), trivial⟩, fun _ _ => ⟨rfl, rfl⟩⟩

example : ¬ stepPre unsupportedHooks (fun _ _ => True) true (fun _ => True) noError entry := by
  intro safe
  exact safe.2 () trivial

end MiriTests.Verification.StepWP

/-! Check that default vcgen selects the opcode rules for symbolic inputs. -/
namespace MiriTests.Verification.InstructionSpecs

open Miri.Interpreter Miri.MIR Miri.Verification.StepWP Std.WP
set_option experimental.vcgen true
variable {P L E M C V : Type}
local notation "S" => StepState P L E M
local notation "H" => StepHooks P L E M C V

example (hooks : H) (allowed : S → C → Prop) (post : Unit → S → Prop)
    (onError : StepError → S → Prop) (before : S)
    (matched : (Instruction.statement .Nop).matches before) (enabled : ∃ c, allowed before c)
    (next : ∀ frame loc, before.stack.currentFrame? = some frame → frame.location = .mir loc →
      post () (afterNop before frame loc)) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.statement .Nop))
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  exact ⟨matched, enabled, next⟩

example (hooks : H) (allowed : S → C → Prop) (destination : Place) (rhs : Rvalue)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) (before : S)
    (matched : (Instruction.statement (.Assign destination rhs)).matches before)
    (next : transitionPre allowed true
      (fun c => Step.finishStatement (before.stack.frames.size - 1) (hooks.assign c destination rhs before))
      (post ()) onError before) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.statement (.Assign destination rhs)))
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  exact ⟨matched, next⟩

example (hooks : H) (allowed : S → C → Prop) (target : BasicBlockId) (hints : Array LoopHintAttr)
    (post : Unit → S → Prop) (onError : StepError → S → Prop) (before : S) (term : Terminator)
    (selected : currentTerminator before = some term) (kind : term.kind = .Goto target hints)
    (next : transitionPre allowed true (fun c => Step.runTerminator hooks c term before)
      (post ()) onError before) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) (.goto target hints))
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  exact ⟨term, selected, kind, next⟩

example (hooks : H) (allowed : S → C → Prop) (post : Unit → S → Prop)
    (onError : StepError → S → Prop) (before : S) (term : Terminator)
    (selected : currentTerminator before = some term) (kind : term.kind = .Return)
    (next : transitionPre allowed true (fun c => Step.runTerminator hooks c term before)
      (post ()) onError before) :
    Triple (Program.instruction (hooks := hooks) (allowed := allowed) .ret)
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  exact ⟨term, selected, kind, next⟩

end MiriTests.Verification.InstructionSpecs
