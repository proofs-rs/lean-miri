import Miri.Concurrency.Thread

open Miri.Concurrency

private def stateCode (thread : ThreadRecord) : String :=
  match thread.state with
  | .Enabled => "enabled"
  | .Terminated => "terminated"
  | .Blocked (.Join id) _ callback => s!"blocked-join-{id.toNat}-cb-{callback}"
  | .Blocked _ _ callback => s!"blocked-cb-{callback}"

private def lookupCode (manager : ThreadManager) (raw : Nat) : String :=
  match manager.threadIdTryFrom raw with
  | .ok id => s!"ok-{id.toNat}"
  | .error .invalidId => "invalid"
  | .error (.terminated id) => s!"terminated-{id.toNat}"
  | .error _ => "other-error"

private def statusCode (status : ThreadJoinStatus) : String :=
  match status with
  | .Joinable => "Joinable"
  | .Detached => "Detached"
  | .Joined => "Joined"

private def threadScenario : Except ThreadError (List String) := do
  let manager := ThreadManager.initial false
  let (created, child) ← ThreadManager.createThread manager 42
  let childRecord ← match ThreadManager.thread? created child with
    | none => .error .invalidId
    | some record => .ok record
  let createLine := s!"create:{child.toNat}:{stateCode childRecord}:{statusCode childRecord.joinStatus}:{created.liveThreadCount}"

  let (lookupOne, _) ← ThreadManager.createThread manager 1
  let (lookup, dead) ← ThreadManager.createThread lookupOne 2
  let deadRecord ← match ThreadManager.thread? lookup dead with
    | none => .error .invalidId
    | some record => .ok record
  let deadThreads := lookup.threads.set dead.toNat { deadRecord with state := .Terminated }
  let lookup := { lookup with threads := deadThreads }
  let lookupLines := [
    s!"lookup:0:{lookupCode lookup 0}",
    s!"lookup:1:{lookupCode lookup 1}",
    s!"lookup:2:{lookupCode lookup 2}",
    s!"lookup:3:{lookupCode lookup 3}",
    s!"lookup:4294967296:{lookupCode lookup 4294967296}",
    s!"live:{lookup.liveThreadCount}"]

  let (active, child) ← ThreadManager.createThread manager 3
  let (active, previous) ← ThreadManager.setActiveThread active child
  let activeLine := s!"active:{previous.toNat}:{active.activeThread.toNat}"

  let (blocked, joiner) ← ThreadManager.createThread manager 4
  let blocked ← ThreadManager.blockThread blocked (.Join joiner) none 77
  let mainRecord ← match ThreadManager.thread? blocked ThreadId.MAIN_THREAD with
    | none => .error .invalidId
    | some record => .ok record
  let blockLine := s!"block:{stateCode mainRecord}"

  let (detachable, child) ← ThreadManager.createThread manager 5
  let detachedResult := ThreadManager.detachThread detachable child false
  let detached ← detachedResult
  let detachedRecord ← match ThreadManager.thread? detached child with
    | none => .error .invalidId
    | some record => .ok record
  let secondDetach := (ThreadManager.detachThread detached child false).isOk
  let detachLine := s!"detach:true:{statusCode detachedRecord.joinStatus}:{secondDetach}"

  pure ([createLine] ++ lookupLines ++ [activeLine, blockLine, detachLine])

def main : IO Unit := do
  match threadScenario with
  | .error _ => IO.println "thread:error"
  | .ok lines => for line in lines do IO.println line
