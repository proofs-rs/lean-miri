import Miri.Interpreter.RunLoop
open Miri.Interpreter Miri.Concurrency
namespace RunTests
structure State where
  events : List Nat := []
  callbackPresent : Bool := true
  origin : Nat := 9
  deriving DecidableEq, Repr

def log (n : Nat) (s : State) : State := { s with events := s.events ++ [n] }
def hooks (core : Except StepError Bool := .ok false)
    (poll : Except StepError StackEmptyPoll := .ok .pending)
    (interrupt := false) (communicate := false)
    (action : RunSchedulingAction := .executeStep) : RunLoopHooks State Unit Unit where
  coreStep := fun _ s => (log 1 s, core)
  takeStackEmptyCallback := fun s => ({ s with callbackPresent := false, origin := 0 }, .ok ())
  invokeStackEmptyCallback := fun _ _ s =>
    if s.callbackPresent then (s, .error (.invalidProgram "recursive callback"))
    else (log 3 s, poll)
  restoreStackEmptyCallback := fun _ s => ({ s with callbackPresent := true }, .ok ())
  terminateActiveThread := fun _ forExit s =>
    if forExit then (s, .error (.invalidProgram "for_exit"))
    else if !s.callbackPresent then (s, .error (.invalidProgram "terminate before restore"))
    else (log 5 s, .ok ())
  interrupted := fun _ => interrupt
  handleAbnormalTermination := log 7
  schedule := fun _ s => (log 6 s, .ok action)
  communicate := fun _ => communicate
  pollAndUnblock := fun _ _ s => (log 8 s, .ok ())
  sleep := fun _ _ s => (log 9 s, .ok ())

example : (RunLoop.stepCurrentThread hooks () {}).1.events = [1,3] := by decide
example : (RunLoop.stepCurrentThread hooks () {}).1.callbackPresent = true := by decide
example : (RunLoop.stepCurrentThread hooks () {}).1.origin = 0 := by decide
-- Empty core stack and Pending succeed without thread termination or program exit.
example : (RunLoop.stepCurrentThread hooks () {}).2 = .ok () := by decide
example : (RunLoop.stepCurrentThread (hooks (.ok false) (.ok .ready)) () {}).1.events = [1,3,5] := by decide
example : (RunLoop.stepCurrentThread (hooks (.ok true)) () {}).1.events = [1] := by decide
example : (RunLoop.stepCurrentThread (hooks (.error (.undefinedBehavior "core"))) () {}).1.origin = 9 := by decide
example : (RunLoop.stepCurrentThread (hooks (.error (.undefinedBehavior "core"))) () {}).1.events = [1] := by decide
example : (RunLoop.stepCurrentThread (hooks (.ok false) (.error (.undefinedBehavior "callback"))) () {}).1.callbackPresent = false := by decide
example : (RunLoop.stepCurrentThread (hooks (.ok false) (.error (.undefinedBehavior "callback"))) () {}).1.events = [1,3] := by decide
example : (RunLoop.iteration (hooks (.ok false) (.ok .pending) true) () {}).1.events = [7] := by decide
example : (RunLoop.iteration (hooks (.ok false) (.ok .pending) true) () {}).2 = .error (.termination .interrupted) := by decide
example : (RunLoop.iteration (hooks (.ok false) (.ok .pending) false true (.sleepAndWaitForIo none)) () {}).1.events = [6,8] := by decide
example : (RunLoop.iteration (hooks (.ok false) (.ok .pending) false false (.sleepAndWaitForIo (some 10))) () {}).1.events = [6,9] := by decide
example : (RunLoop.iteration (hooks (.ok false) (.ok .pending) false false (.sleepAndWaitForIo none)) () {}).2 = .error (.invalidProgram "infinite isolated sleep") := by decide
example : RunLoop.reportsUB (.termination (.treeBorrowsUb "x")) = true := by decide
example : RunLoop.reportsUB (.termination .interrupted) = false := by decide
example : RunLoop.reportsUB (.termination (.exit 0 true)) = false := by decide
def takeFail : RunLoopHooks State Unit Unit := { hooks with
  takeStackEmptyCallback := fun s => (log 2 s, .error (.invalidProgram "take")) }
example : (RunLoop.stepCurrentThread takeFail () {}).1.events = [1,2] := by decide
example : (RunLoop.stepCurrentThread (hooks (.ok false) (.ok .ready)) () {}).2 = .ok () := by decide
-- Only the termination hook can produce a program exit; Pending is not an exit.
def exits : RunLoopHooks State Unit Unit := { hooks (.ok false) (.ok .ready) with
  terminateActiveThread := fun _ _ s => (log 5 s, .error (.termination (.exit 0 true))) }
example : (RunLoop.stepCurrentThread exits () {}).2 = .error (.termination (.exit 0 true)) := by decide
-- A checked restoration failure preserves its state mutation and stops before termination.
def restoreFails : RunLoopHooks State Unit Unit := { hooks (.ok false) (.ok .ready) with
  restoreStackEmptyCallback := fun _ s =>
    ({ log 4 s with callbackPresent := true }, .error (.invalidProgram "restore")) }
example : (RunLoop.stepCurrentThread restoreFails () {}).1.events = [1,3,4] := by decide
example : (RunLoop.stepCurrentThread restoreFails () {}).1.callbackPresent = true := by decide
example : (RunLoop.stepCurrentThread restoreFails () {}).2 =
    .error (.invalidProgram "restore") := by decide
end RunTests
