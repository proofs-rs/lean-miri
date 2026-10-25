import Miri.Concurrency.AtomicDispatch

open Miri.ABI Miri.Memory Miri.Concurrency

private def ix0 : VectorIdx := VectorIdx.ofU32 0 (by decide)
private def ix1 : VectorIdx := VectorIdx.ofU32 1 (by decide)
private def t0 : VTimestamp := VTimestamp.ZERO
private def size (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)
private def range4 : AllocRange := ⟨size 0, size 4⟩
private def range2 : AllocRange := ⟨size 0, size 2⟩

private def currentClock (global : GlobalState) (threads : ThreadManager) :
    Except GlobalStateError VClock := do
  let (_, thread) ← global.activeThreadState threads
  pure thread.clock

private def valLabel : Option Nat → String
  | none => "U"
  | some value => toString value

def main : IO Unit := do
  let manager0 := ThreadManager.initial false
  let (manager1, worker) ← match manager0.createThread 123 with
    | .error _ => throw (IO.userError "source thread creation failed")
    | .ok result => pure result
  let base := GlobalState.initial true true
  let global ← match base.threadCreated manager1 worker none with
    | .error _ => throw (IO.userError "source vector-clock creation failed")
    | .ok state => pure state
  let (managerMain, _) ← match manager1.setActiveThread ThreadId.MAIN_THREAD with
    | .error _ => throw (IO.userError "could not activate main thread")
    | .ok result => pure result
  let managerWorker := match manager1.setActiveThread worker with
    | .error _ => manager1
    | .ok (next, _) => next
  let allocation := VClockAlloc.newAllocation (ByteSize.ofU64 4 (by decide)) t0 ix0
  let initial : AtomicState Nat := {
    global := global
    allocation := allocation
    weakMemoryAllocation := some (StoreBufferAlloc.newAllocation) }

  -- The source store hook runs after the vanilla memory write. Validation
  -- records the atomic access and increments the global clock before the
  -- weak-memory hook snapshots the release clock and appends its store.
  let stored := atomicStoreState initial managerMain range4 .Release 11 (some 0)
  let storedState ← match stored.outcome with
    | .error _ => throw (IO.userError "atomic store state transition failed")
    | .ok _ => pure stored.state
  let storeCount := match storedState.weakMemoryAllocation with
    | none => 0
    | some buffers => buffers.bufferCount
  if storeCount != 1 then throw (IO.userError "atomic store did not create one exact buffer")

  -- The worker has not yet acquired the release store. A differently-sized
  -- atomic access must stop at the first byte and preserve the pre-validation
  -- thread clock instead of reporting a successful load.
  let beforeRace ← match currentClock storedState.global managerWorker with
    | .error _ => throw (IO.userError "worker clock missing before mixed-size load")
    | .ok clock => pure clock
  let mixed := bufferedAtomicRead storedState managerWorker range2 .Acquire 11 0
  match mixed.outcome with
  | .error (.validation .race) => pure ()
  | _ => throw (IO.userError "unordered mixed-size load did not report a race")
  let afterRace ← match currentClock mixed.state.global managerWorker with
    | .error _ => throw (IO.userError "worker clock missing after mixed-size load")
    | .ok clock => pure clock
  if beforeRace != afterRace then
    throw (IO.userError "failed atomic validation incremented the active thread clock")
  IO.println "validation:mixed-size-race:state-preserved"

  -- The chosen buffer entry supplies the release clock to validation. Load
  -- metadata is recorded only after the acquire transition and its clock bump.
  let loaded := bufferedAtomicRead storedState managerWorker range4 .Acquire 11 0
  let loadResult ← match loaded.outcome with
    | .error _ => throw (IO.userError "buffered acquire load failed")
    | .ok result => pure result
  if loadResult.value != some 11 then
    throw (IO.userError "buffered acquire load returned the wrong stored value")
  let choice ← match loadResult.choice with
    | none => throw (IO.userError "buffered acquire load used memory fallback")
    | some choice => pure choice
  if choice.recency != .Latest then
    throw (IO.userError "rank zero did not select newest modification-order entry")
  let postLoadClock ← match currentClock loaded.state.global managerWorker with
    | .error _ => throw (IO.userError "worker clock missing after acquire load")
    | .ok clock => pure clock
  let loadedElement := match loaded.state.weakMemoryAllocation with
    | none => none
    | some buffers =>
      match buffers.getStoreBuffer range4 with
      | .ok (some handle) => handle.buffer.entries.find?
          (fun (entry : StoreElement Nat) => entry.val == some 11)
      | _ => none
  let loadTimestamp := loadedElement.bind fun element => element.loadInfo.timestampFor? ix1
  if loadTimestamp != some (postLoadClock.index ix1) then
    throw (IO.userError "load metadata was not recorded with the post-validation clock")
  let loadTime := match loadTimestamp with | none => 0 | some timestamp => timestamp.time
  IO.println s!"dispatch:read:{valLabel loadResult.value}:Latest:{loadTime}:{(postLoadClock.index ix1).time}"

  -- Miri validates the RMW first, then the weak-memory hook reads metadata
  -- from the latest buffered store and appends the computed new value.
  let rmw := atomicRmwState loaded.state managerWorker range4 .AcqRel 11 12
  let rmwState ← match rmw.outcome with
    | .error _ => throw (IO.userError "acqrel RMW state transition failed")
    | .ok _ => pure rmw.state
  let entries := match rmwState.weakMemoryAllocation with
    | none => []
    | some buffers =>
      match buffers.getStoreBuffer range4 with
      | .ok (some handle) => handle.buffer.entries.map fun entry => entry.val
      | _ => []
  if entries != [some 0, some 11, some 12] then
    throw (IO.userError s!"RMW modification order was {entries}")
  let rmwMetadata := match rmwState.weakMemoryAllocation with
    | none => (0, false)
    | some buffers =>
      match buffers.getStoreBuffer range4 with
      | .ok (some handle) =>
        match handle.buffer.entries.find? (fun (entry : StoreElement Nat) => entry.val == some 11) with
        | none => (0, false)
        | some entry =>
          let time := ((entry.loadInfo.timestampFor? ix1).map VTimestamp.time).getD 0
          (time, entry.loadInfo.scLoaded)
      | _ => (0, false)
  IO.println s!"dispatch:rmw:{String.intercalate "," (entries.map valLabel)}:load-ts{rmwMetadata.1}:sc{if rmwMetadata.2 then 1 else 0}"

  -- A sequentially-consistent store records its SC clock after successful
  -- validation and retains the per-byte release clock in the new store.
  let scStore := atomicStoreState rmwState managerMain range4 .SeqCst 13 (some 12)
  let scState ← match scStore.outcome with
    | .error _ => throw (IO.userError "SeqCst store state transition failed")
    | .ok _ => pure scStore.state
  let mainClock ← match currentClock scState.global managerMain with
    | .error _ => throw (IO.userError "main clock missing after SeqCst store")
    | .ok clock => pure clock
  let lastSc := scState.global.lastScWritePerThread.index ix0
  if lastSc != mainClock.index ix0 then
    throw (IO.userError "SeqCst store did not publish the post-validation clock")
  let newStore := match scState.weakMemoryAllocation with
    | none => none
    | some buffers =>
      match buffers.getStoreBuffer range4 with
      | .ok (some handle) => handle.buffer.entries.find?
          (fun (entry : StoreElement Nat) => entry.val == some 13)
      | _ => none
  let storeTime := (newStore.map fun entry => entry.storeTimestamp.time).getD 0
  let storeIsSc := (newStore.map fun entry => entry.isSeqCst).getD false
  let storeSync := (newStore.map fun entry => (entry.syncClock.index ix0).time).getD 0
  IO.println s!"dispatch:store:13:{storeTime}:{if storeIsSc then 1 else 0}:{storeSync}"

  let fallbackState := { scState with weakMemoryAllocation := none }
  let fallback := bufferedAtomicRead fallbackState managerMain range4 .SeqCst 13 0
  match fallback.outcome with
  | .error _ => throw (IO.userError "SeqCst latest-memory fallback failed")
  | .ok result =>
    if result.value != some 13 || result.choice.isSome then
      throw (IO.userError "missing weak-memory allocation did not use latest-value fallback")
  IO.println "load:fallback:latest-memory:sc-read-applied"
