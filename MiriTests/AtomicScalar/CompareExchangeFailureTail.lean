import Miri.Interpreter.IntrinsicAtomic
import Miri.MIR.Syntax

open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
open Miri.Interpreter

private def ix0 : VectorIdx := VectorIdx.ofU32 0 (by decide)
private def ix1 : VectorIdx := VectorIdx.ofU32 1 (by decide)
private def allocId : AllocId := ⟨1, by decide⟩
private def rangeFor (bytes : Nat) : AllocRange :=
  ⟨Size.ZERO, Size.ofBytes (UInt64.ofNat bytes)⟩
private def stamp (n : Nat) : VTimestamp :=
  (VTimestamp.ofTime n).toOption.getD VTimestamp.ZERO
private def scalar (value bytes : Nat) : Scalar Provenance :=
  (Scalar.fromUInt (BitVec.ofNat 128 value) (Size.ofBytes (UInt64.ofNat bytes))).toOption.getD
    (Scalar.fromBool false)
private def dataLayout (bytes : Nat) : TyAndLayout Nat := ⟨bytes, {
  fields := .Primitive, variants := .Single 0, backendRepr := .Memory (sized := true),
  largestNiche := none, uninhabited := false, align := .new Align.ONE,
  size := Size.ofBytes (UInt64.ofNat bytes), maxReprAlign := none,
  unadjustedAbiAlign := Align.ONE, reprC := false, randomizationSeed := 0 }⟩

private structure FixtureState where
  global : Option GlobalState
  atomic : AtomicState (Scalar Provenance)
  physical : Scalar Provenance
  failPhysicalRead : Bool := false
  physicalReads : Nat := 0

private def stub {α : Type} : RvalueM FixtureState α :=
  throw (.unsupported "unused atomic fixture hook")

private def scalarOps : ScalarOpsHooks Provenance FixtureState Unit := {
  classify := fun _ ty => pure (.integer (if ty == 2 then .u16 else .u8))
  boolLayout := fun _ => pure (dataLayout 1)
  orderingLayout := fun _ => pure (dataLayout 1)
  overflowLayout := fun _ layout => pure layout
  metadataLayout := fun _ _ => pure (dataLayout 1)
  unitLayout := fun _ => pure (dataLayout 0)
  floatBinary := fun _ _ _ _ => stub
  pointerBinary := fun _ _ _ _ => stub
  floatUnary := fun _ _ _ => stub
  derefValidity := fun _ _ => stub }

private def hooks : AtomicAccessHooks Provenance FixtureState Unit Nat := {
  target := ⟨.little, .w64⟩
  getGlobal := FixtureState.global
  setGlobal := fun state global =>
    { state with global := some global, atomic := { state.atomic with global := global } }
  threads := fun _ => ThreadManager.initial false
  getAtomic := fun state _ => .ok state.atomic
  setAtomic := fun _ atomic => modify fun state => { state with atomic := atomic }
  placeLayout := dataLayout
  placePointer := fun _ => .ok (Pointer.new (some (.concrete allocId BorTag.one)) Size.ZERO)
  physicalRead := fun _ place => do
    modify fun state => { state with physicalReads := state.physicalReads + 1 }
    if (← get).failPhysicalRead then throw (.callback "fixture physical read")
    return ⟨.scalar (← get).physical, dataLayout place⟩
  physicalWrite := fun _ value _ => do
    match value with
    | .scalar scalar => modify fun state => { state with physical := scalar }
    | _ => throw (.invalidProgram "atomic fixture expected a scalar write")
  ghostRead := fun _ _ => pure none
  checkPointerAlign := fun _ _ _ => pure ()
  resolveAllocation := fun _ _ => pure (allocId, Size.ZERO)
  mutability := fun _ _ => pure Miri.Memory.Mutability.Mut
  scalarOps := scalarOps
  loadChoiceRank := fun _ _ => pure 0
  weakPolicy := .neverFail
  weakSuccessChoice := fun _ => pure false
  diagnostic := fun _ _ => pure ()
  classifyDispatchError := fun error => .invalidProgram (reprStr error)
  classifyGlobalError := fun error => .invalidProgram (reprStr error) }

private def makeState (bytes current : Nat) (weakMemory multiThreaded backend : Bool) : FixtureState := Id.run do
  let base := GlobalState.initial false weakMemory
  let global := { base with
    multiThreaded := multiThreaded
    lastScFence := VClock.newWithIndex ix1 (stamp 7) }
  let value := scalar current bytes
  let buffers :=
    if weakMemory then
      some ((StoreBufferAlloc.newAllocation : StoreBufferAlloc (Scalar Provenance))
        |>.getOrCreateStoreBuffer (rangeFor bytes) (some value)).allocation
    else none
  let atomic : AtomicState (Scalar Provenance) := {
    global := global
    allocation := VClockAlloc.newAllocation
      (ByteSize.ofU64 2 (by decide)) VTimestamp.ZERO ix0
    weakMemoryAllocation := buffers }
  return {
    global := (if backend then some global else none)
    atomic := atomic
    physical := value }

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def runFailed (state : FixtureState) (bytes expected : Nat) :=
  IntrinsicAtomic.compareExchange hooks () bytes
    ⟨.scalar (scalar expected bytes), dataLayout bytes⟩
    ⟨.scalar (scalar 99 bytes), dataLayout bytes⟩ false .SeqCst .SeqCst state

private def scReadAtOne (global : GlobalState) : Nat :=
  match global.activeThreadState (ThreadManager.initial false) with
  | .ok (_, clocks) => (clocks.readSeqCst.index ix1).time
  | .error _ => 0

private def checkLatestRead (state : FixtureState) : IO Unit := do
  let some buffers := state.atomic.weakMemoryAllocation
    | throw (IO.userError "actual failed CAS dropped its retained store buffer")
  let handle ← match buffers.getStoreBuffer (rangeFor 1) with
    | .ok (some handle) => pure handle
    | _ => throw (IO.userError "actual failed CAS lost its exact-range buffer")
  check (handle.buffer.last.loadInfo.timestampFor? ix0).isSome
    "actual failed CAS did not record latest-buffer read metadata"
  check handle.buffer.last.loadInfo.scLoaded
    "actual failed CAS did not record latest-buffer SeqCst metadata"

def main : IO Unit := do
  -- Connected production IntrinsicAtomic.compareExchange path: vector clocks
  -- remain installed after Miri's inactive/single-thread fast path. There is no
  -- weak-memory backend or allocation buffer in this case.
  let noBuffer := makeState 1 7 false false true
  let (failed, afterNoBuffer) ← match runFailed noBuffer 1 8 with
    | .ok result state => pure (result, state)
    | .error error _ => throw (IO.userError s!"inactive failed CAS errored: {repr error}")
  check (!failed.2 && failed.1.toUInt8 == .ok 7) "inactive failed CAS returned wrong old/success result"
  let some noBufferGlobal := afterNoBuffer.global
    | throw (IO.userError "vector-clock global disappeared")
  check (scReadAtOne noBufferGlobal == 7)
    "actual inactive failed CAS missed the SeqCst read mark without weak memory"

  -- The same production path commits the read metadata of a retained latest
  -- weak-memory store, even though race detection is inactive.
  let buffered := makeState 1 7 true false true
  let (failed, afterBuffered) ← match runFailed buffered 1 8 with
    | .ok result state => pure (result, state)
    | .error error _ => throw (IO.userError s!"buffered failed CAS errored: {repr error}")
  check (!failed.2 && failed.1.toUInt8 == .ok 7) "buffered failed CAS result changed"
  checkLatestRead afterBuffered

  -- A failed CAS without vector-clock support must not enter the hook tail.
  let noBackend := makeState 1 7 false false false
  let (failed, afterNoBackend) ← match runFailed noBackend 1 8 with
    | .ok result state => pure (result, state)
    | .error error _ => throw (IO.userError s!"backend-free failed CAS errored: {repr error}")
  check (!failed.2 && failed.1.toUInt8 == .ok 7) "backend-free CAS result changed"
  check (scReadAtOne afterNoBackend.atomic.global == 0)
    "backend-free CAS unexpectedly applied vector-clock SC bookkeeping"

  -- A successful CAS continues to use its old write path and does not run the
  -- failed-CAS SC/latest-buffer tail.
  let successful := makeState 1 7 true true true
  let (result, afterSuccess) ← match
      IntrinsicAtomic.compareExchange hooks () 1
        ⟨.scalar (scalar 7 1), dataLayout 1⟩
        ⟨.scalar (scalar 9 1), dataLayout 1⟩ false .SeqCst .SeqCst successful with
    | .ok result state => pure (result, state)
    | .error error _ => throw (IO.userError s!"successful CAS errored: {repr error}")
  check (result.2 && result.1.toUInt8 == .ok 7) "successful CAS result changed"
  check (afterSuccess.physical.toUInt8 == .ok 9) "successful CAS failed to write replacement"
  let some successGlobal := afterSuccess.global
    | throw (IO.userError "successful CAS lost vector-clock state")
  check (scReadAtOne successGlobal == 7) "successful SeqCst CAS lost its source RMW read mark"
  let some successBuffers := afterSuccess.atomic.weakMemoryAllocation
    | throw (IO.userError "successful CAS dropped weak-memory state")
  let successHandle ← match successBuffers.getStoreBuffer (rangeFor 1) with
    | .ok (some handle) => pure handle
    | _ => throw (IO.userError "successful CAS buffer disappeared")
  check (successHandle.buffer.last.val == some (scalar 9 1))
    "successful CAS did not append its replacement to modification order"
  check (successHandle.buffer.last.loadInfo.timestampFor? ix0).isNone
    "successful CAS incorrectly ran the failed-CAS latest-read tail on its new store"

  -- A physical read callback can mutate its state prefix and then fail. The
  -- connected atomic path must return that prefix while restoring the source
  -- data-race-free window.
  let readFailure := { makeState 1 7 false false true with failPhysicalRead := true }
  match runFailed readFailure 1 8 with
  | .ok _ _ => throw (IO.userError "physical-read failure was swallowed")
  | .error (.callback "fixture physical read") afterReadFailure => do
    check (afterReadFailure.physicalReads == 1) "physical-read error lost its callback prefix"
    check (!(afterReadFailure.global.map GlobalState.ongoingActionDataRaceFree).getD true)
      "physical-read error failed to restore allow_data_races"
  | .error error _ => throw (IO.userError s!"wrong physical-read error: {repr error}")

  -- Validation fails on byte two after mutating atomic metadata for byte one;
  -- the actual IntrinsicAtomic dispatch must preserve the helper's error state.
  let base := makeState 2 7 false true true
  let laterWrite := stamp 99
  let allocation := base.atomic.allocation
  let cell ← match allocation.cellAt 1 with
    | .ok cell => pure cell
    | .error _ => throw (IO.userError "fixture second clock cell missing")
  let allocation ← match allocation.setCell 1 { cell with write := (ix0, laterWrite), writeType := .Write } with
    | .ok allocation => pure allocation
    | .error _ => throw (IO.userError "fixture second clock cell could not be set")
  let raceGlobal := { base.atomic.global with multiThreaded := true }
  let raceState := { base with
    global := some raceGlobal
    atomic := { base.atomic with global := raceGlobal, allocation := allocation } }
  match runFailed raceState 2 8 with
  | .ok _ _ => throw (IO.userError "second-byte atomic validation race was swallowed")
  | .error _ afterRace => do
    let first ← match afterRace.atomic.allocation.cellAt 0 with
      | .ok cell => pure cell
      | .error _ => throw (IO.userError "first clock cell vanished after error")
    let second ← match afterRace.atomic.allocation.cellAt 1 with
      | .ok cell => pure cell
      | .error _ => throw (IO.userError "second clock cell vanished after error")
    check first.atomicOps.isSome "validation error discarded its first-byte state prefix"
    check second.atomicOps.isSome "validation error discarded the failing-byte mutation"

  IO.println "atomic-cas-failure-tail:intrinsic-connected:PASS"
