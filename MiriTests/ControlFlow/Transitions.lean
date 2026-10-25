import Miri.Interpreter.ControlFlow
import Lean.Elab.Tactic
open Miri.MIR Miri.Interpreter Miri.ABI
namespace ControlTests
abbrev S := StepState Unit Unit Unit (List Nat)
abbrev H := TerminatorHooks Unit Unit Unit (List Nat) Unit Unit Nat

def log (n : Nat) (s : S) : S := { s with machine := s.machine ++ [n] }
def hooks (action : ReturnAction := .normal) : H where
  bodySpan := fun _ => .ok ⟨123⟩
  returnOperand := fun _ s => (log 1 s, .ok ())
  popFrame := fun _ s => match s.stack.popFrame with
    | .error e => (log 2 s, .error (.stack e))
    | .ok (stack, frame) => (log 2 { s with stack }, .ok frame)
  copyReturn := fun _ _ _ s => (log 3 s, .ok ())
  cleanupFrame := fun _ _ _ s => (log 4 s, .ok action)
  unwindTerminate := fun _ _ s => (log 5 s, .ok ())
  evalDiscriminant := fun _ _ s => (log 6 s, .ok 20)
  compareSwitchCase := fun _ value bits s => (log bits s, .ok (value == bits))
  call := fun _ _ s => (s, .error (.unsupported "test call"))
  tailCall := fun _ _ s => (s, .error (.unsupported "test tailcall"))
  drop := fun _ _ _ _ s => (s, .error (.unsupported "test drop"))
  ignoreOptionalOverflowChecks := fun _ => true
  readAssertCondition := fun _ _ s => (log 7 s, .error (.undefinedBehavior "condition read"))
  assertPanic := fun _ _ _ s => (log 8 s, .ok ())

def source : SourceInfo := ⟨⟨0⟩, 0⟩
def block (statements : Array Statement) (kind : TerminatorKind) (cleanup := false) : BasicBlock :=
  ⟨statements, ⟨source, kind⟩, cleanup⟩
def prep (f : Frame Unit Unit Unit) (continuation : ReturnContinuation)
    (location : FrameLocation := .mir ⟨0, 0⟩) : Frame Unit Unit Unit :=
  { f with
    location := location
    returnContinuation := continuation
    body := { f.body with basicBlocks := #[block #[] .Return] } }
def pair (f : Frame Unit Unit Unit) : S :=
  ⟨⟨#[prep f (.stop true), prep f (.goto (some 8) .Continue)]⟩, []⟩
def root (f : Frame Unit Unit Unit) : S := ⟨⟨#[prep f (.stop true)]⟩, []⟩

example (f : Frame Unit Unit Unit) :
    (ControlFlow.returnFromCurrentFrame hooks.toControlHooks () false (pair f)).1.machine = [1,2,3,4] := rfl
example (f : Frame Unit Unit Unit) :
    (ControlFlow.returnFromCurrentFrame hooks.toControlHooks () false (pair f)).1.stack.currentFrame?.map (·.location) =
      some (.mir ⟨8,0⟩) := rfl
example (f : Frame Unit Unit Unit) :
    (ControlFlow.returnFromCurrentFrame (hooks .noJump).toControlHooks () false (pair f)).1.stack.currentFrame?.map (·.location) =
      some (.mir ⟨0,0⟩) := rfl
example (f : Frame Unit Unit Unit) :
    (ControlFlow.returnFromCurrentFrame (hooks .noCleanup).toControlHooks () false (root f)).2 = .ok () := rfl
example (f : Frame Unit Unit Unit) :
    (ControlFlow.returnFromCurrentFrame (hooks .noCleanup).toControlHooks () false (pair f)).2 =
      .error (.invalidProgram "NoCleanup requires empty stack and normal return") := rfl
example (f : Frame Unit Unit Unit) :
    let s : S := ⟨⟨#[prep f (.stop true) (.unwinding ⟨0⟩)]⟩, []⟩
    (ControlFlow.returnFromCurrentFrame hooks.toControlHooks () true s).1.machine = [] := rfl
example (f : Frame Unit Unit Unit) :
    let s : S := ⟨⟨#[prep f (.stop true), prep f (.goto none (.Cleanup 7)) (.unwinding ⟨0⟩)]⟩, []⟩
    (ControlFlow.returnFromCurrentFrame hooks.toControlHooks () true s).1.machine = [1,2,4] := rfl
example (f : Frame Unit Unit Unit) :
    let s : S := ⟨⟨#[prep f (.stop true), prep f (.goto none (.Cleanup 7)) (.unwinding ⟨0⟩)]⟩, []⟩
    (ControlFlow.returnFromCurrentFrame hooks.toControlHooks () true s).1.stack.currentFrame?.map (·.location) =
      some (.mir ⟨7,0⟩) := rfl
example (f : Frame Unit Unit Unit) :
    (ControlFlow.unwindToBlock hooks.toControlHooks () (.Terminate .Abi) (root f)).1.stack.currentFrame?.map (·.location) =
      some (.unwinding ⟨123⟩) := rfl

def discr : Miri.MIR.Operand := .Copy ⟨0, #[]⟩
def switch : Terminator := ⟨source, .SwitchInt discr ⟨#[.Case 10 1, .Case 20 2, .Case 30 3], 4⟩⟩
example (f : Frame Unit Unit Unit) :
    (ControlFlow.evalTerminator hooks () switch (root f)).1.machine = [6,10,20] := rfl
example (f : Frame Unit Unit Unit) :
    (ControlFlow.evalTerminator hooks () switch (root f)).1.stack.currentFrame?.map (·.location) = some (.mir ⟨2,0⟩) := rfl
example (f : Frame Unit Unit Unit) :
    (ControlFlow.evalTerminator hooks () ⟨source, .Assert discr true (.OverflowNeg discr) 5 .Continue⟩ (root f)).2 =
      .error (.undefinedBehavior "condition read") := rfl

def stepHooks : StepHooks Unit Unit Unit (List Nat) Unit Unit where
  assign := fun _ _ _ s => (s, .error (.unsupported "assign"))
  evalPlace := fun _ _ _ s => (s, .error (.unsupported "place"))
  writeDiscriminant := fun _ _ _ s => (s, .error (.unsupported "discriminant"))
  storageLive := fun _ _ s => (s, .error (.unsupported "live"))
  storageDead := fun _ _ s => (s, .error (.unsupported "dead"))
  intrinsic := fun _ _ s => (s, .error (.unsupported "intrinsic"))
  incrementConstEvalCounter := fun _ s => (s, .error (.unsupported "counter"))
  returnFromCurrentFrame := fun c u => ControlFlow.returnFromCurrentFrame hooks.toControlHooks c u
  beforeTerminator := fun _ s => (log 9 s, .ok ())
  terminator := fun c t => ControlFlow.evalTerminator hooks c t

def program (f : Frame Unit Unit Unit) : S :=
  let f := prep f (.stop true)
  ⟨⟨#[{ f with body := { f.body with basicBlocks :=
    #[block #[] (.Goto 1 #[]), block #[⟨source, .Nop⟩] .Return] } }]⟩, []⟩
def run3 (s : S) : S :=
  (Step.step stepHooks () (Step.step stepHooks () (Step.step stepHooks () s).1).1).1
def fixtureBody : Body := ⟨.Built, 0, none, #[0], #[]⟩
def fixtureBodies : Array Body := #[fixtureBody]
def fixtureLoaded : LoadedBody := ⟨BodyIdentity.ofCanonicalIndex 0, fixtureBodies[0]⟩
def returnLayout : LocalLayout := ⟨fixtureBody.locals[0], {
    fields := .Primitive, variants := .Single 0, backendRepr := .Memory (sized := true),
    largestNiche := none, uninhabited := false, align := .new Align.ONE, size := Size.ZERO,
    maxReprAlign := none, unadjustedAbiAlign := Align.ONE, reprC := false, randomizationSeed := 0 }⟩
def fixtureIdentity : LocalsIdentity := (LocalsIdentitySupply.allocate ⟨0⟩).2
def fixture : Frame Unit Unit Unit where
  body := fixtureLoaded.body
  bodyIdentity := fixtureLoaded.identity
  functionInstance := ⟨.Item 0, #[]⟩
  extra := ()
  returnContinuation := .stop true
  returnPlace := .frameLocal 0 0 none returnLayout fixtureIdentity
  localsIdentity := fixtureIdentity
  locals := #[]
  vaList := #[]
  trackCallerArg := none
  location := .mir ⟨0,0⟩
example : (run3 (program fixture)).stack.frames.size = 0 := by decide
example : (run3 (program fixture)).machine = [9,9,1,2,3,4] := by decide
example : (Step.step stepHooks () (run3 (program fixture))).2 = .ok false := by decide
def copyFailHooks : H := { hooks with copyReturn := fun _ _ _ s =>
  (log 3 s, .error (.undefinedBehavior "copy")) }
example : (ControlFlow.returnFromCurrentFrame copyFailHooks.toControlHooks () false (pair fixture)).1.machine = [1,2,3] := by decide
example : (ControlFlow.returnFromCurrentFrame copyFailHooks.toControlHooks () false (pair fixture)).1.stack.frames.size = 1 := by decide
example : (ControlFlow.returnFromCurrentFrame hooks.toControlHooks () true
    ⟨⟨#[prep fixture (.stop true) (.unwinding ⟨0⟩)]⟩, []⟩).2 =
      .error (.undefinedBehavior "unwinding past the topmost stack frame") := by decide
example : (ControlFlow.returnToBlock none (root fixture)).2 = .error (.undefinedBehavior "Unreachable") := by decide

def terminatingHooks : H := { hooks with unwindTerminate := fun _ _ s => ControlFlow.goToBlock 99 (log 5 s) }
example : (ControlFlow.unwindToBlock terminatingHooks.toControlHooks () (.Terminate .Abi) (root fixture)).1.stack.currentFrame?.map (·.location) =
    some (.mir ⟨99,0⟩) := by decide
example : (ControlFlow.unwindToBlock hooks.toControlHooks () .Continue (root fixture)).1.stack.currentFrame?.map (·.location) =
    some (.unwinding ⟨123⟩) := by decide
example : ControlFlow.isOptionalOverflowCheck (.Overflow .AddUnchecked discr discr) = false := by decide
example : ControlFlow.isOptionalOverflowCheck (.Overflow .Add discr discr) = true := by decide
end ControlTests
