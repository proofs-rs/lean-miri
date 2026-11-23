import Miri.Verification.ExactWP
import MiriTests.ControlFlow.Transitions

namespace MiriTests.Verification.CallReturnWP

open Miri.MIR Miri.Interpreter Miri.Verification.StepWP Std.WP

set_option experimental.vcgen true

private def callKind : TerminatorKind :=
  .Call ControlTests.discr #[] ⟨0, #[]⟩ (some 1) .Continue .Normal ⟨0⟩

private def callee : Frame Unit Unit Unit :=
  ControlTests.prep ControlTests.fixture (.goto (some 1) .Continue)

private def terminators : ControlTests.H := { ControlTests.hooks with
  call := fun _ _ state =>
    match state.stack.pushFrame callee with
    | .ok stack => (ControlTests.log 10 { state with stack }, .ok ())
    | .error error => (state, .error (.stack error)) }

private def hooks := { ControlTests.stepHooks with
  terminator := fun choice term => ControlFlow.evalTerminator terminators choice term }

private def caller : Frame Unit Unit Unit := { ControlTests.fixture with
  body := { ControlTests.fixture.body with
    basicBlocks := #[ControlTests.block #[] callKind, ControlTests.block #[] .Return] } }

private def entry : ControlTests.S := ⟨⟨#[caller]⟩, []⟩

private abbrev DriverProgram := Program hooks (fun _ _ => True)
private def invoke : DriverProgram :=
  .instruction (.terminator (.Call ControlTests.discr #[] ⟨0, #[]⟩ (some 1) .Continue .Normal ⟨0⟩))
private def ret : DriverProgram := .instruction .ret
private def afterCall : ControlTests.S := ⟨⟨#[caller, callee]⟩, [9, 10]⟩
private def afterReturn : ControlTests.S :=
  ⟨⟨#[{ caller with location := .mir ⟨1, 0⟩ }]⟩, [9, 10, 9, 1, 2, 3, 4]⟩

private theorem returnToCaller (post : Unit → ControlTests.S → Prop) (completed : post () afterReturn) :
    Triple ret (· = afterCall) post (fun _ _ => False) := by
  vcgen [ret]
  subst_vars
  refine ⟨_, rfl, rfl, ⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  exact ⟨rfl, completed⟩

/-- The call callback pushes a frame in this fixture. The actual driver and
return transition resume the caller, and the client chooses its final post. -/
theorem callReturn (post : Unit → ControlTests.S → Prop) (completed : post () afterReturn) :
    Triple (Program.seq invoke ret) (· = entry) post (fun _ _ => False) := by
  vcgen [invoke, ret]
  subst_vars
  refine ⟨_, rfl, rfl, ⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  change true = true ∧ wp ret post (fun _ _ => False) afterCall
  exact ⟨rfl, Triple.iff.mp (returnToCaller post completed) afterCall rfl⟩

/-- The canonical machine selects its production rule with arbitrary success
and error continuations. -/
example {K U C O X Host : Type} [DecidableEq K]
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (allowed : MachineHooks.State K U → C → Prop)
    (post : Bool → MachineHooks.State K U → Prop) (onError : StepError → MachineHooks.State K U → Prop) :
    Triple (OutcomeStep.step (hooks := ExecutionMachine.stepHooks config limits) (allowed := allowed))
      (Miri.Verification.CanonicalStepWP.outcomePre config limits allowed post onError) post onError := by
  vcgen <;> assumption

end MiriTests.Verification.CallReturnWP
