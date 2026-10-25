import Miri.Interpreter.Scheduling
open Miri.Interpreter Miri.Concurrency
namespace SchedulingQA
structure State where
  manager : ThreadManager := ThreadManager.initial true
  events : List Nat := []
  communicate : Bool := false

def log (n : Nat) (state : State) : State := { state with events := state.events ++ [n] }
def hooks (fail : Bool := false) : SchedulingHooks State Unit where
  manager := (·.manager)
  setManager := fun manager state => { state with manager }
  communicate := (·.communicate)
  -- Exercise the required re-read of settings after environment callbacks.
  processDelayedReadiness := fun _ state =>
    let state := log 1 { state with communicate := true }
    (state, if fail then .error (.callback "readiness") else .ok ())
  pollNonBlocking := fun _ state => (log 2 state, .ok ())
  unblockExpiredDeadlines := fun _ state => (log 3 state, .ok (some 10))
  anyThreadBlockedOnHost := fun _ => false
  threadRank := fun _ _ => 0

def yielding : State := { manager := { ThreadManager.initial true with yieldActiveThread := true } }
example : (Scheduling.localSchedule hooks () ({} : State)).1.events = [] := by decide
example : (Scheduling.localSchedule hooks () yielding).1.events = [1,2,3] := by decide
example : (Scheduling.localSchedule hooks () yielding).2 = .ok .executeStep := by decide
example : (Scheduling.localSchedule (hooks true) () yielding).1.events = [1] := by decide
example : (Scheduling.localSchedule (hooks true) () yielding).2 = .error (.callback "readiness") := by decide
example : (Scheduling.localSchedule (hooks true) () yielding).1.communicate = true := by decide
def pollFails : SchedulingHooks State Unit := { hooks with
  pollNonBlocking := fun _ state => (log 2 state, .error (.callback "poll")) }
def deadlineFails : SchedulingHooks State Unit := { hooks with
  unblockExpiredDeadlines := fun _ state => (log 3 state, .error (.callback "deadline")) }
example : (Scheduling.localSchedule pollFails () yielding).1.events = [1,2] := by decide
example : (Scheduling.localSchedule deadlineFails () yielding).1.events = [1,2,3] := by decide
example : (Scheduling.localSchedule pollFails () yielding).2 = .error (.callback "poll") := by decide
example : (Scheduling.localSchedule deadlineFails () yielding).2 = .error (.callback "deadline") := by decide
end SchedulingQA
