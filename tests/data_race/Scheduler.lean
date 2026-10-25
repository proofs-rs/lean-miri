import Miri.Concurrency.Scheduler

open Miri.Concurrency

def tid0 : ThreadId := ThreadId.ofU32 0 (by decide)
def tid1 : ThreadId := ThreadId.ofU32 1 (by decide)
def tid2 : ThreadId := ThreadId.ofU32 2 (by decide)

def enabledThread : ThreadRecord := ThreadRecord.initial none none
def blockedThread : ThreadRecord :=
  { enabledThread with state := .Blocked .IO none 9 }
def terminatedThread : ThreadRecord :=
  { enabledThread with state := .Terminated }

def manager3 (fixed : Bool) : ThreadManager := {
  activeThread := tid0
  threads := [enabledThread, blockedThread, enabledThread]
  threadLocalAllocs := []
  yieldActiveThread := true
  fixedScheduling := fixed
}

def deadlockedManager : ThreadManager := {
  activeThread := tid0
  threads := [blockedThread, terminatedThread]
  threadLocalAllocs := []
  yieldActiveThread := false
  fixedScheduling := false
}

def allTerminatedManager : ThreadManager := {
  activeThread := tid0
  threads := [terminatedThread]
  threadLocalAllocs := []
  yieldActiveThread := false
  fixedScheduling := true
}

def fastManager : ThreadManager :=
  { manager3 true with yieldActiveThread := false }

def ids (threadIds : List ThreadId) : String :=
  String.intercalate "," (threadIds.map fun id => toString id.toNat)

def sourceChoiceOrderCode (manager : ThreadManager) : String :=
  match Scheduler.eligibleThreads manager with
  | .error _ => "error"
  | .ok threadIds => ids threadIds

def scheduleCode (result : Except SchedulerError SchedulerAction) : String :=
  match result with
  | .error _ => "error"
  | .ok (.executeStep _ thread choices) => s!"execute:{thread.toNat}:choices={ids choices}"
  | .ok (.sleepAndWaitForIo _ (some duration)) => s!"sleep:{duration}"
  | .ok (.sleepAndWaitForIo _ none) => "sleep:indefinite"
  | .ok (.globalDeadlock _) => "deadlock"
  | .ok (.allThreadsTerminatedInvariant _) => "all-terminated-invariant"

def actionNames (actions : List SchedulerEnvironmentAction) : String :=
  String.intercalate "," (actions.map fun action => match action with
    | .processDelayedReadiness => "readiness"
    | .pollHostIoNonBlocking => "poll"
    | .unblockExpiredDeadlines => "deadlines")

def planCode (result : Except SchedulerError SchedulerPlan) : String :=
  match result with
  | .error _ => "error"
  | .ok (.executeCurrent _) => "execute-current"
  | .ok (.serviceEnvironment _ communicate actions) =>
    s!"environment:communicate={communicate}:actions={actionNames actions}"

example : sourceChoiceOrderCode (manager3 true) = "2,0" := by
  decide

example : planCode (Scheduler.plan (manager3 true) true) =
    "environment:communicate=true:actions=readiness,poll,deadlines" := by
  decide

example : planCode (Scheduler.plan (manager3 true) false) =
    "environment:communicate=false:actions=readiness,deadlines" := by
  decide

example : planCode (Scheduler.plan fastManager false) = "execute-current" := by
  decide

example : scheduleCode (Scheduler.finishLocal (manager3 true) none false 99) =
    "execute:2:choices=2,0" := by
  decide

example : scheduleCode (Scheduler.finishLocal (manager3 false) none false 1) =
    "execute:0:choices=2,0" := by
  decide

example : scheduleCode (Scheduler.finishLocal (manager3 false) none false 2) = "error" := by
  decide

example : scheduleCode (Scheduler.finishLocal deadlockedManager none false 0) = "deadlock" := by
  decide

example : scheduleCode (Scheduler.finishLocal deadlockedManager (some 17) false 0) = "sleep:17" := by
  decide

example : scheduleCode (Scheduler.finishLocal deadlockedManager none true 0) = "sleep:indefinite" := by
  decide

example : scheduleCode (Scheduler.finishLocal allTerminatedManager none false 0) =
    "all-terminated-invariant" := by
  decide

def main : IO Unit := do
  IO.println s!"scheduler:candidates:{sourceChoiceOrderCode (manager3 false)}"
  IO.println s!"scheduler:fixed:{scheduleCode (Scheduler.finishLocal (manager3 true) none false 0)}"
  IO.println s!"scheduler:choice1:{scheduleCode (Scheduler.finishLocal (manager3 false) none false 1)}"
  IO.println s!"scheduler:choice-error:{scheduleCode (Scheduler.finishLocal (manager3 false) none false 2)}"
  IO.println s!"scheduler:deadline:{scheduleCode (Scheduler.finishLocal deadlockedManager (some 17) false 0)}"
  IO.println s!"scheduler:host-io:{scheduleCode (Scheduler.finishLocal deadlockedManager none true 0)}"
  IO.println s!"scheduler:deadlock:{scheduleCode (Scheduler.finishLocal deadlockedManager none false 0)}"
