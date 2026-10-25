import Miri.Interpreter.Step
import Lean.Elab.Tactic
open Miri.MIR Miri.Interpreter
namespace StepTests
abbrev S := StepState Unit Unit Unit (List Nat)
abbrev H := StepHooks Unit Unit Unit (List Nat) Unit Unit

def event (n : Nat) (fail : Bool) (s : S) : StepResult S Unit :=
  ({ s with machine := s.machine ++ [n] }, if fail then .error (.callback "stop") else .ok ())
def hooks (fail : Bool := false) : H where
  assign := fun _ _ _ => event 1 fail
  evalPlace := fun _ _ skip s =>
    let r := event (if skip then 99 else 2) fail s
    (r.1, r.2)
  writeDiscriminant := fun _ _ _ => event 3 fail
  storageLive := fun _ _ => event 4 fail
  storageDead := fun _ _ => event 5 fail
  intrinsic := fun _ _ => event 6 fail
  incrementConstEvalCounter := fun _ => event 7 fail
  returnFromCurrentFrame := fun _ unwinding => event (if unwinding then 8 else 99) fail
  beforeTerminator := fun _ => event 9 fail
  terminator := fun _ _ => event 10 fail

def source : SourceInfo := ⟨⟨0⟩, 0⟩
def stmt (kind : StatementKind) : Statement := ⟨source, kind⟩
def empty : S := ⟨Stack.empty, []⟩
example : (Step.step hooks () empty).2 = .ok false := by decide
example : (Step.evalStatement hooks () (stmt .Nop) empty).1.machine = [] := by decide
example : (Step.evalStatement (hooks true) () (stmt (.StorageLive 0)) empty).1.machine = [4] := by decide
example : (Step.evalStatement (hooks true) () (stmt (.StorageLive 0)) empty).2 =
    .error (.callback "stop") := by decide
example : (Step.evalStatement hooks () (stmt (.SetDiscriminant ⟨0, #[]⟩ 0)) empty).1.machine = [2, 3] := by decide
example : (Step.evalStatement (hooks true) () (stmt (.SetDiscriminant ⟨0, #[]⟩ 0)) empty).1.machine = [2] := by decide
example : (Step.evalStatement hooks () (stmt (.PlaceMention ⟨0, #[]⟩)) empty).1.machine = [2] := by decide

-- A supplied frame's opaque metadata is irrelevant to driver order.
def prepared (frame : Frame Unit Unit Unit) (statements : Array Statement)
    (location : FrameLocation := .mir ⟨0, 0⟩) : S :=
  ⟨⟨#[{ frame with location, body := { frame.body with basicBlocks :=
    #[⟨statements, ⟨source, .Unreachable⟩, false⟩] } }]⟩, []⟩
example (frame : Frame Unit Unit Unit) :
    (Step.step hooks () (prepared frame #[] (.unwinding ⟨0⟩))).1.machine = [8] := by rfl
example (frame : Frame Unit Unit Unit) :
    (Step.step hooks () (prepared frame #[])).1.machine = [9, 10] := by rfl
example (frame : Frame Unit Unit Unit) :
    (Step.step (hooks true) () (prepared frame #[])).1.machine = [9] := by rfl
example (frame : Frame Unit Unit Unit) :
    (Step.step hooks () (prepared frame #[stmt .Nop])).1.stack.currentFrame?.map
      (fun f => f.location) = some (.mir ⟨0, 1⟩) := by rfl
example (frame : Frame Unit Unit Unit) :
    (Step.step (hooks true) () (prepared frame #[stmt (.StorageLive 0)])).1.stack.currentFrame?.map
      (fun f => f.location) = some (.mir ⟨0, 0⟩) := by rfl
example (cause : FakeReadCause) (place : Place) :
    Step.evalStatement hooks () (stmt (.FakeRead cause place)) empty = (empty, .ok ()) := rfl
example (place : Place) (projection : UserTypeProjection) (variance : Variance) :
    Step.evalStatement hooks () (stmt (.AscribeUserType place projection variance)) empty = (empty, .ok ()) := rfl
example (coverage : CoverageKind) :
    Step.evalStatement hooks () (stmt (.Coverage coverage)) empty = (empty, .ok ()) := rfl
example (place : Place) (reason : BackwardIncompatibleDropReason) :
    Step.evalStatement hooks () (stmt (.BackwardIncompatibleDropHint place reason)) empty = (empty, .ok ()) := rfl

def changedLocationHooks : H := { hooks with
  storageLive := fun _ _ s =>
    match s.stack.updateCurrentLocation (.mir ⟨0, 1⟩) with
    | .ok stack => ({ s with stack }, .ok ())
    | .error e => (s, .error (.stack e)) }
example (frame : Frame Unit Unit Unit) :
    (Step.step changedLocationHooks ()
      (prepared frame #[stmt (.StorageLive 0), stmt .Nop])).1.stack.currentFrame?.map
      (fun f => f.location) = some (.mir ⟨0, 2⟩) := by rfl

def changedFrameHooks : H := { hooks with storageLive := fun _ _ s =>
  ({ s with stack := { frames := s.stack.frames ++ s.stack.frames } }, .ok ()) }
example (frame : Frame Unit Unit Unit) :
    (Step.step changedFrameHooks () (prepared frame #[stmt (.StorageLive 0)])).2 =
      .error (.frameIndexChanged 0 1) := by rfl

def failingTerminatorHooks : H := { hooks with terminator := fun _ _ => event 10 true }
example (frame : Frame Unit Unit Unit) :
    (Step.step failingTerminatorHooks () (prepared frame #[])).1.machine = [9, 10] := by rfl
example (frame : Frame Unit Unit Unit) :
    (Step.step failingTerminatorHooks () (prepared frame #[])).2 = .error (.callback "stop") := by rfl
end StepTests
