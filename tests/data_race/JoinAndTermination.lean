import Miri.Concurrency

open Miri.Concurrency

private def reportName : TerminationReport → String
  | .regularExit code leaks => s!"exit:{code}:leaks={leaks}"
  | .abnormalTermination => "abort"
  | .interrupted => "interrupted"
  | .unsupportedOperation => "unsupported"
  | .undefinedBehavior => "ub"
  | .globalDeadlock => "global-deadlock"
  | .localDeadlock => "local-deadlock"
  | .otherMachineStop => "other-machine-stop"

private def managerOf : JoinPlan → ThreadManager := JoinPlan.manager

private def joinScenario : Except String (List String) := do
  let initial := ThreadManager.initial false
  let (created, child) ← (ThreadManager.createThread initial 90).mapError (fun _ => "create")
  let returnValue : JoinReturn := { scalarToken := 11, placeToken := 12 }
  let waiting ← (ThreadManager.prepareJoin created child returnValue .none 700)
    |>.mapError (fun _ => "prepare join")
  let waitingCompletion ← match waiting with
    | .waiting _ completion => pure completion
    | _ => throw "live thread did not reach wait"
  let waitingLine ← match waiting with
    | .waiting manager completion => do
      let joiner ← match manager.thread? ThreadId.MAIN_THREAD with
        | some record => pure record
        | none => throw "missing joiner"
      let joinee ← match manager.thread? child with
        | some record => pure record
        | none => throw "missing joinee"
      pure s!"wait:{joiner.isBlockedOn (.Join child)}:joined={joinee.joinStatus == .Joined}:capture={completion.callbackToken}:{completion.returnValue.placeToken}"
    | _ => throw "live thread did not reach wait"

  let (onChild, _) ← (ThreadManager.setActiveThread (managerOf waiting) child)
    |>.mapError (fun _ => "activate child")
  let (terminated, termination) ← (ThreadManager.beginTerminateActive onChild false .Ready)
    |>.mapError (fun _ => "begin termination")
  let continuation ← (ThreadManager.completeTlsCleanup terminated termination [])
    |>.mapError (fun _ => "complete empty TLS cleanup")
  let finish ← (afterTlsCleanup .none continuation)
    |>.mapError (fun _ => "finish TLS stage")
  let wakePlan ← match finish with
    | .wakeJoiners manager gone waiters =>
      (ThreadManager.beginJoinerWakeups manager gone waiters).mapError (fun _ => "wake joiner")
    | _ => throw "wrong no-handler finish stage"
  let wakeLine ← match wakePlan with
    | .invokeCallback _manager gone unblock remaining => do
      let completion ← (ThreadManager.afterJoinUnblock
        waitingCompletion unblock)
        |>.mapError (fun _ => "validate join callback")
      pure s!"wake:{unblock.target.toNat}:{unblock.previousActive.toNat}:gone={gone.toNat}:reason={unblock.reason == .Join child}:remaining={remaining.length}:ready={unblock.kind == .Ready}:capture={completion.callbackToken}"
    | _ => throw "expected one joiner callback"

  let childRecord ← match created.thread? child with
    | some record => pure record
    | none => throw "missing immediate joinee"
  let immediateManager := { created with
    threads := created.threads.set child.toNat { childRecord with state := .Terminated } }
  let immediate ← (ThreadManager.prepareJoin immediateManager child returnValue .vectorClocks 701)
    |>.mapError (fun _ => "prepare completed join")
  let immediateLine := match immediate with
    | .completedImmediately manager completion =>
      let status := (manager.thread? child).map (fun t => t.joinStatus == .Joined)
      s!"immediate:{status == some true}:handler={completion.handler == .vectorClocks}:place={completion.returnValue.placeToken}"
    | _ => "immediate:unexpected-non-immediate"

  let exclusiveSelf := ThreadManager.prepareJoinExclusive initial ThreadId.MAIN_THREAD
    returnValue .none 702
  let selfLine := match exclusiveSelf with
    | .error (.selfJoinUb _) => "exclusive-self:ub"
    | _ => "exclusive-self:unexpected"
  pure [waitingLine, wakeLine, immediateLine, selfLine]

def main : IO Unit := do
  let examples : List (String × TerminationInfo) := [
    ("exit", .exit 7 true), ("abort", .abort "panic"), ("interrupt", .interrupted),
    ("isolation", .unsupportedInIsolation "host call"),
    ("sb", .stackedBorrowsUb "invalid access"), ("tb", .treeBorrowsUb "invalid access"),
    ("strict-provenance", .int2PtrWithStrictProvenance),
    ("global", .globalDeadlock), ("local", .localDeadlock),
    ("symbols", .multipleSymbolDefinitions "f"),
    ("shim", .symbolShimClashing "f"), ("race", .dataRace true),
    ("foreign", .unsupportedForeignItem "f")]
  for (name, info) in examples do
    IO.println s!"report:{name}:{reportName info.report}:ub={info.isUbReport}"
  match joinScenario with
  | .error error => IO.println s!"join:error:{error}"
  | .ok lines => for line in lines do IO.println line
