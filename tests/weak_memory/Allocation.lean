import Miri.Concurrency.WeakMemory

open Miri.ABI Miri.Memory Miri.Concurrency

private def size (bytes : Nat) : Miri.ABI.Size :=
  Miri.ABI.Size.ofBytes (UInt64.ofNat bytes)

private def range (start length : Nat) : AllocRange :=
  allocRange (size start) (size length)

private def outcomeCode (result : Except StoreBufferAllocError (Option (StoreBufferHandle Nat))) :
    String :=
  match result with
  | .error _ => "error"
  | .ok none => "none"
  | .ok (some handle) =>
    let latestValue := handle.buffer.last.val
    s!"some:{handle.position}:{handle.buffer.entries.length}:{match latestValue with | none => "U" | some value => toString value}"

def main : IO Unit := do
  let empty : StoreBufferAlloc Nat := .newAllocation
  IO.println s!"lookup:empty:{match empty.getStoreBuffer (range 4 4) with | .error _ => "error" | .ok none => "none" | .ok (some _) => "some"}"

  let created := empty.getOrCreateStoreBuffer (range 4 4) (some 7)
  IO.println s!"create:{outcomeCode created.outcome}:{created.allocation.bufferCount}"
  match created.outcome with
  | .error _ => IO.println "lookup:exact:error"
  | .ok none => IO.println "lookup:exact:missing"
  | .ok (some handle) =>
    IO.println s!"lookup:exact:{outcomeCode (.ok (some handle))}"
    IO.println s!"lookup:partial:{match created.allocation.getStoreBuffer (range 5 1) with | .error _ => "error" | .ok none => "none" | .ok (some _) => "some"}"

  let protectedGlobal := GlobalState.withDataRaceFreeAction
    (GlobalState.initial false false) true
  let protectedWrite := created.allocation.nonAtomicWrite (range 4 4) protectedGlobal
  IO.println s!"non-atomic:protected:{protectedWrite.allocation.bufferCount}"

  let global := GlobalState.initial false false
  let erased := created.allocation.nonAtomicWrite (range 4 4) global
  IO.println s!"non-atomic:perfect:{erased.allocation.bufferCount}"

  let overlapSeed := empty.getOrCreateStoreBuffer (range 4 4) (some 9)
  match overlapSeed.outcome with
  | .error _ => IO.println "overlap:seed-error"
  | .ok none => IO.println "overlap:seed-missing"
  | .ok (some _) =>
    let replaced := overlapSeed.allocation.getOrCreateStoreBuffer (range 3 2) (some 11)
    IO.println s!"overlap:replace:{outcomeCode replaced.outcome}:{replaced.allocation.bufferCount}"
    let partialWrite := replaced.allocation.nonAtomicWrite (range 2 3) global
    IO.println s!"non-atomic:partial:{partialWrite.allocation.bufferCount}"
