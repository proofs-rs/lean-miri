import Miri.Concurrency.AtomicDispatch

/-! # Bounded SC store-buffering transition projection

This executable projection runs the repository's actual `GlobalState`,
`AtomicDispatch`, and `WeakMemory` definitions. It constructs two children with
the real `threadCreated` transition, explores all six total orders respecting
each worker's store-before-load order, and branches on every candidate rank
returned by `StoreBuffer.fetchChoices` at each load. It separately tracks the
latest scalar memory value, as the interpreter does before the buffered-load
hook.

This is not a connected MIR scheduler graph. The scheduler is projected to the
six atomic event orders; each worker has no additional atomic event, and there
are no mutexes, fences, callbacks, address choices, or other memory accesses in
this projection. See README.md for the explicit runtime-to-projection
obligations and the source-pinned Miri reference boundary.
-/

open Miri.ABI Miri.Memory Miri.Concurrency

namespace ScProjection202

private def ix0 : VectorIdx := VectorIdx.ofU32 0 (by decide)
private def ix1 : VectorIdx := VectorIdx.ofU32 1 (by decide)
private def thread0 : ThreadId := ThreadId.ofU32 0 (by decide)
private def thread1 : ThreadId := ThreadId.ofU32 1 (by decide)
private def thread2 : ThreadId := ThreadId.ofU32 2 (by decide)
private def size (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)
private def rangeX : AllocRange := ⟨size 0, size 4⟩
private def rangeY : AllocRange := ⟨size 0, size 4⟩

inductive Ordering where
  | seqCst
  | relaxed
  deriving DecidableEq, BEq, Repr

inductive Event where
  | aStore
  | aLoad
  | bStore
  | bLoad
  deriving DecidableEq, BEq, Repr

private def allOrders : List (List Event) := [
  [.aStore, .aLoad, .bStore, .bLoad],
  [.aStore, .bStore, .aLoad, .bLoad],
  [.aStore, .bStore, .bLoad, .aLoad],
  [.bStore, .aStore, .aLoad, .bLoad],
  [.bStore, .aStore, .bLoad, .aLoad],
  [.bStore, .bLoad, .aStore, .aLoad]
]

private def firstScStoreBuffer : StoreBuffer Nat :=
  (StoreBuffer.new (some 0)).storeImpl 1 ix1 ThreadClockSet.default.clock true VClock.default

-- Kernel-check the real `storeImpl` for this initial-clock state: the zero
-- initial write is marked SC and the first store leaves two entries.
theorem first_sc_store_marks_initial_write :
    firstScStoreBuffer.oldest.isSeqCst = true := by decide

theorem first_sc_store_retains_one_newer_write :
    firstScStoreBuffer.newer.length = 1 := by decide

-- A kernel-checked query against the actual `fetchChoices` implementation at
-- this concrete two-entry buffer and default reader clocks. The all-clock
-- strengthening is proved independently in `SelectorProof195.lean` for
-- arbitrary writer and reader clocks. Runtime enumeration here still covers
-- every candidate at all six event orders in the operational projection.
theorem first_sc_default_clock_load_selects_newer :
    (StoreBuffer.fetchChoices firstScStoreBuffer true ThreadClockSet.default).map
      (fun choice => (choice.position, choice.element.val)) = [(1, some 1)] := by
  conv => lhs; cbv

private structure ProjectionState where
  global : GlobalState
  allocationX : VClockAlloc
  allocationY : VClockAlloc
  buffersX : StoreBufferAlloc Nat
  buffersY : StoreBufferAlloc Nat
  threads : ThreadManager
  latestX : Nat := 0
  latestY : Nat := 0
  readA : Option Nat := none
  readB : Option Nat := none

private def makeInitial : Except String ProjectionState := do
  let manager0 := ThreadManager.initial false
  let (manager1, a) ← (manager0.createThread 101).mapError fun e => s!"create A: {reprStr e}"
  let (manager2, b) ← (manager1.createThread 102).mapError fun e => s!"create B: {reprStr e}"
  let global0 := GlobalState.initial true true
  let global1 ← (global0.threadCreated manager1 a none).mapError fun e => s!"vector clock A: {reprStr e}"
  let global2 ← (global1.threadCreated manager2 b none).mapError fun e => s!"vector clock B: {reprStr e}"
  -- These are separate source allocations, as in the fixture's two AtomicU32s.
  let allocationX := VClockAlloc.newAllocation
    (ByteSize.ofU64 4 (by decide)) VTimestamp.ZERO ix0
  let allocationY := VClockAlloc.newAllocation
    (ByteSize.ofU64 4 (by decide)) VTimestamp.ZERO ix0
  let buffersX := StoreBufferAlloc.newAllocation
  let buffersY := StoreBufferAlloc.newAllocation
  let (threads, _) ← (manager2.setActiveThread thread0).mapError fun e => s!"activate main: {reprStr e}"
  pure { global := global2, allocationX, allocationY, buffersX, buffersY, threads }

private def atomicX (state : ProjectionState) : AtomicState Nat := {
  global := state.global
  allocation := state.allocationX
  weakMemoryAllocation := some state.buffersX }

private def atomicY (state : ProjectionState) : AtomicState Nat := {
  global := state.global
  allocation := state.allocationY
  weakMemoryAllocation := some state.buffersY }

private def commitX (state : ProjectionState) (atomic : AtomicState Nat) : ProjectionState :=
  { state with
    global := atomic.global
    allocationX := atomic.allocation
    buffersX := atomic.weakMemoryAllocation.getD state.buffersX }

private def commitY (state : ProjectionState) (atomic : AtomicState Nat) : ProjectionState :=
  { state with
    global := atomic.global
    allocationY := atomic.allocation
    buffersY := atomic.weakMemoryAllocation.getD state.buffersY }

private def activate (state : ProjectionState) (thread : ThreadId) : Except String ProjectionState := do
  let (threads, _) ← (state.threads.setActiveThread thread).mapError fun e => s!"activate {thread.value.val}: {reprStr e}"
  pure { state with threads := threads }

private def readValue (value : Option Nat) (event : Event) : Except String Nat :=
  match value with
  | none => .error s!"{reprStr event} selected an uninitialized store"
  | some n => .ok n

private def loadOrd : Ordering → AtomicReadOrd
  | .seqCst => .SeqCst
  | .relaxed => .Relaxed

private def storeOrd : Ordering → AtomicWriteOrd
  | .seqCst => .SeqCst
  | .relaxed => .Relaxed

private def executeEvent (ordering : Ordering) (event : Event)
    (state : ProjectionState) : Except String (List ProjectionState) := do
  match event with
  | .aStore => do
      let active ← activate state thread1
      let stored := atomicStoreState (atomicX active) active.threads rangeX
        (storeOrd ordering) 1 (some 0)
      match stored.outcome with
      | .error failure => throw s!"A store transition failed: {reprStr failure}"
      | .ok _ => pure [{ (commitX active stored.state) with latestX := 1 }]
  | .bStore => do
      let active ← activate state thread2
      let stored := atomicStoreState (atomicY active) active.threads rangeY
        (storeOrd ordering) 1 (some 0)
      match stored.outcome with
      | .error failure => throw s!"B store transition failed: {reprStr failure}"
      | .ok _ => pure [{ (commitY active stored.state) with latestY := 1 }]
  | .aLoad => do
      let active ← activate state thread1
      let prepared := prepareBufferedAtomicRead (atomicY active) active.threads rangeY
        (loadOrd ordering) active.latestY
      match prepared.outcome with
      | .error failure => throw s!"A load prefix failed: {reprStr failure}"
      | .ok (.ready result) => do
          let value ← readValue result.value event
          pure [{ (commitY active prepared.state) with readA := some value }]
      | .ok (.select handle clocks) => do
          let choices := StoreBuffer.fetchChoices handle.buffer
            (ordering == .seqCst) clocks
          if choices.isEmpty then throw "source fetchChoices returned no candidate"
          (List.range choices.length).mapM fun rank => do
            let selected := finishBufferedAtomicRead prepared.state active.threads
              rangeY (loadOrd ordering) handle clocks rank
            match selected.outcome with
            | .error failure => throw s!"A load rank {rank} failed: {reprStr failure}"
            | .ok result => do
                let value ← readValue result.value event
                pure { (commitY active selected.state) with readA := some value }
  | .bLoad => do
      let active ← activate state thread2
      let prepared := prepareBufferedAtomicRead (atomicX active) active.threads rangeX
        (loadOrd ordering) active.latestX
      match prepared.outcome with
      | .error failure => throw s!"B load prefix failed: {reprStr failure}"
      | .ok (.ready result) => do
          let value ← readValue result.value event
          pure [{ (commitX active prepared.state) with readB := some value }]
      | .ok (.select handle clocks) => do
          let choices := StoreBuffer.fetchChoices handle.buffer
            (ordering == .seqCst) clocks
          if choices.isEmpty then throw "source fetchChoices returned no candidate"
          (List.range choices.length).mapM fun rank => do
            let selected := finishBufferedAtomicRead prepared.state active.threads
              rangeX (loadOrd ordering) handle clocks rank
            match selected.outcome with
            | .error failure => throw s!"B load rank {rank} failed: {reprStr failure}"
            | .ok result => do
                let value ← readValue result.value event
                pure { (commitX active selected.state) with readB := some value }

private def runEvents (ordering : Ordering) (events : List Event)
    (states : List ProjectionState) : Except String (List ProjectionState) := do
  match events with
  | [] => pure states
  | event :: rest => do
      let branches ← states.mapM (executeEvent ordering event)
      runEvents ordering rest branches.flatten

private def runOrder (ordering : Ordering) (events : List Event) :
    Except String (List ProjectionState) := do
  let initial ← makeInitial
  runEvents ordering events [initial]

private def stateOutcomes (events : List Event) : List ProjectionState →
    Except String (List (Nat × Nat))
  | [] => .ok []
  | finalState :: rest => do
      let a ← match finalState.readA with
        | none => .error s!"schedule omitted A's read: {reprStr events}"
        | some n => .ok n
      let b ← match finalState.readB with
        | none => .error s!"schedule omitted B's read: {reprStr events}"
        | some n => .ok n
      let tail ← stateOutcomes events rest
      pure ((a, b) :: tail)

private def orderOutcomes (ordering : Ordering) : List (List Event) →
    Except String (List (Nat × Nat))
  | [] => .ok []
  | events :: rest => do
      let finalStates ← runOrder ordering events
      let current ← stateOutcomes events finalStates
      let tail ← orderOutcomes ordering rest
      pure (current ++ tail)

private def runAll (ordering : Ordering) : Except String (List (Nat × Nat)) :=
  orderOutcomes ordering allOrders

def projectedSc : Except String (List (Nat × Nat)) := runAll .seqCst
def projectedRelaxed : Except String (List (Nat × Nat)) := runAll .relaxed

private def noBothZero : Except String (List (Nat × Nat)) → Bool
  | .error _ => false
  | .ok outcomes => outcomes.all (fun result => result != (0, 0))

private def hasBothZero : Except String (List (Nat × Nat)) → Bool
  | .error _ => false
  | .ok outcomes => outcomes.contains (0, 0)

private def before (events : List Event) (first second : Event) : Bool :=
  events.idxOf first < events.idxOf second

-- Kernel-checked linearization sanity lemma. The connected transition run
-- below is executable-checked against Miri's source-extracted candidate rule;
-- this lemma by itself is not the operational connection.
private def serialOutcome (events : List Event) : Nat × Nat :=
  (if before events .bStore .aLoad then 1 else 0,
   if before events .aStore .bLoad then 1 else 0)

theorem six_serial_orders_exclude_both_zero :
    allOrders.all (fun events => serialOutcome events != (0, 0)) = true := by decide

def outcomeText (result : Except String (List (Nat × Nat))) : String :=
  match result with
  | .error reason => s!"error:{reason}"
  | .ok outcomes => s!"{reprStr outcomes}"

def outcomeCompact (outcomes : List (Nat × Nat)) : String :=
  String.intercalate ";" (outcomes.map fun (a, b) => s!"{a},{b}")

end ScProjection202

def main : IO Unit := do
  match ScProjection202.projectedSc with
  | .error reason => throw (IO.userError s!"SeqCst projected transition failed: {reason}")
  | .ok outcomes =>
      if outcomes.contains (0, 0) then
        throw (IO.userError "SeqCst projection produced forbidden (0,0)")
      IO.println s!"projection202:sc:{ScProjection202.outcomeCompact outcomes}"
  match ScProjection202.projectedRelaxed with
  | .error reason => throw (IO.userError s!"Relaxed projected transition failed: {reason}")
  | .ok outcomes =>
      if !outcomes.contains (0, 0) then
        throw (IO.userError "Relaxed projection omitted (0,0)")
      IO.println s!"projection202:relaxed:{ScProjection202.outcomeCompact outcomes}"

#print axioms ScProjection202.six_serial_orders_exclude_both_zero
#print axioms ScProjection202.first_sc_default_clock_load_selects_newer
