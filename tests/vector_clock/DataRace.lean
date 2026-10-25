import Miri.Concurrency.DataRace

open Miri.Concurrency

def ix (value : Nat) (bound : value < 4294967296) : VectorIdx :=
  VectorIdx.ofU32 value bound

def tRead (time : Nat) (bound : 2 * time < 4294967296) : VTimestamp :=
  VTimestamp.ofPacked (2 * time) bound

def tRetag (time : Nat) (bound : 2 * time + 1 < 4294967296) : VTimestamp :=
  VTimestamp.ofPacked (2 * time + 1) bound

def i0 : VectorIdx := ix 0 (by decide)
def i1 : VectorIdx := ix 1 (by decide)
def i2 : VectorIdx := ix 2 (by decide)
def z : VTimestamp := tRead 0 (by decide)
def t1 : VTimestamp := tRead 1 (by decide)
def t2 : VTimestamp := tRead 2 (by decide)

def clockAt (index : VectorIdx) (timestamp : VTimestamp) : VClock :=
  VClock.newWithIndex index timestamp

def threadWith (index : VectorIdx) (timestamp : VTimestamp) : ThreadClockSet :=
  { ThreadClockSet.default with clock := clockAt index timestamp }

def oneByte : ByteSize := ByteSize.ofU64 1 (by decide)
def twoBytes : ByteSize := ByteSize.ofU64 2 (by decide)
def fourBytes : ByteSize := ByteSize.ofU64 4 (by decide)
def eightBytes : ByteSize := ByteSize.ofU64 8 (by decide)

def zeroOffset : ByteSize := ByteSize.ofU64 0 (by decide)

def codeResult : DataRaceResult → String
  | .ok => "ok"
  | .race => "race"
  | .invalidClockUpdate _ => "clock-error"
  | .internalInvariantViolation => "invariant-error"
  | .outOfBounds => "out-of-bounds"

def codeNaReadType : NaReadType → String
  | .Read => "read"
  | .Retag => "retag"

def codeNaWriteType : NaWriteType → String
  | .Allocate => "allocate"
  | .Write => "write"
  | .Retag => "retag"
  | .Deallocate => "deallocate"

def packedAt (clock : VClock) (index : VectorIdx) : Nat :=
  (clock.index index).packedValue

def atomicSizeCode (cell : MemoryCellClocks) : String :=
  match cell.atomicOps with
  | none => "none"
  | some atomic =>
    match atomic.size with
    | none => "mixed-reads"
    | some size => toString size.bytes

def orderingCode : AtomicOrdering → String
  | .Relaxed => "relaxed"
  | .Acquire => "acquire"
  | .Release => "release"
  | .AcqRel => "acqrel"
  | .SeqCst => "seqcst"

def readOrderCode : Except AtomicOrderingError AtomicReadOrd → String
  | .ok .Relaxed => "relaxed"
  | .ok .Acquire => "acquire"
  | .ok .SeqCst => "seqcst"
  | .error (.invalidRead _) => "invalid"
  | .error _ => "wrong-error"

def writeOrderCode : Except AtomicOrderingError AtomicWriteOrd → String
  | .ok .Relaxed => "relaxed"
  | .ok .Release => "release"
  | .ok .SeqCst => "seqcst"
  | .error (.invalidWrite _) => "invalid"
  | .error _ => "wrong-error"

def fenceOrderCode : Except AtomicOrderingError AtomicFenceOrd → String
  | .ok .Acquire => "acquire"
  | .ok .Release => "release"
  | .ok .AcqRel => "acqrel"
  | .ok .SeqCst => "seqcst"
  | .error (.invalidFence _) => "invalid"
  | .error _ => "wrong-error"

def atomicReadClockAt (cell : MemoryCellClocks) (index : VectorIdx) : String :=
  match cell.atomicOps with
  | none => "missing-atomic-state"
  | some atomic => toString (packedAt atomic.readVector index)

def atomicWriteClockAt (cell : MemoryCellClocks) (index : VectorIdx) : String :=
  match cell.atomicOps with
  | none => "missing-atomic-state"
  | some atomic => toString (packedAt atomic.writeVector index)

def atomicSyncClockAt (cell : MemoryCellClocks) (index : VectorIdx) : String :=
  match cell.atomicOps with
  | none => "missing-atomic-state"
  | some atomic => toString (packedAt atomic.syncVector index)

example :
    (VClockAlloc.readNonAtomic
      (VClockAlloc.newAllocation twoBytes z i0)
      { start := oneByte, size := twoBytes }
      (threadWith i0 t1) i0 .Read).result = .outOfBounds := by
  decide

def main : IO Unit := do
  for ordering in [AtomicOrdering.Relaxed, .Acquire, .Release, .AcqRel, .SeqCst] do
    let read := AtomicReadOrd.ofOrdering ordering
    let write := AtomicWriteOrd.ofOrdering ordering
    let fence := AtomicFenceOrd.ofOrdering ordering
    IO.println s!"ordering:{orderingCode ordering}:{readOrderCode read}:{writeOrderCode write}:{fenceOrderCode fence}"

  let fenced := ThreadClockSet.applyReleaseFence
    { ThreadClockSet.default with clock := clockAt i0 t1 }
  IO.println s!"fence:release:{packedAt fenced.fenceRelease i0}"
  let acquired := ThreadClockSet.applyAcquireFence
    { ThreadClockSet.default with
      clock := clockAt i0 t1
      fenceAcquire := clockAt i0 t2 }
  IO.println s!"fence:acquire:{packedAt acquired.clock i0}"

  let initialCell := MemoryCellClocks.new t2 i0
  let olderThread := threadWith i0 t1
  let retagRead := MemoryCellClocks.nonAtomicReadDetect initialCell olderThread i0 .Retag
  IO.println s!"cell:retag-race:{codeResult retagRead.result}:{packedAt retagRead.thread.clock i0}:{codeNaReadType (retagRead.thread.clock.index i0).readType}"

  let orderedThread := threadWith i0 (tRead 3 (by decide))
  let readOk := MemoryCellClocks.nonAtomicReadDetect
    (MemoryCellClocks.new t1 i0) orderedThread i0 .Read
  IO.println s!"cell:non-atomic-read:{codeResult readOk.result}:{packedAt readOk.cell.read i0}"

  let atomicRead := MemoryCellClocks.atomicReadDetect
    (MemoryCellClocks.new z i0) (threadWith i1 t1) i1 fourBytes
  IO.println s!"cell:atomic-read:{codeResult atomicRead.result}:{atomicSizeCode atomicRead.cell}:{atomicReadClockAt atomicRead.cell i1}"

  let unorderedMixedWrite := MemoryCellClocks.atomicWriteDetect
    atomicRead.cell (threadWith i0 t1) i0 eightBytes
  IO.println s!"cell:mixed-size-write-race:{codeResult unorderedMixedWrite.result}:{atomicSizeCode unorderedMixedWrite.cell}"

  let orderedSizeChange := MemoryCellClocks.atomicWriteDetect
    atomicRead.cell (threadWith i1 t2) i1 eightBytes
  IO.println s!"cell:ordered-size-change:{codeResult orderedSizeChange.result}:{atomicSizeCode orderedSizeChange.cell}:{atomicWriteClockAt orderedSizeChange.cell i1}"

  let differentSizeRead := MemoryCellClocks.atomicReadDetect
    atomicRead.cell (threadWith i0 t1) i0 eightBytes
  IO.println s!"cell:mixed-size-reads:{codeResult differentSizeRead.result}:{atomicSizeCode differentSizeRead.cell}"

  let racingAtomicWrite := MemoryCellClocks.atomicWriteDetect
    readOk.cell (threadWith i2 t1) i2 fourBytes
  IO.println s!"cell:atomic-write-race:{codeResult racingAtomicWrite.result}:{atomicWriteClockAt racingAtomicWrite.cell i2}"

  let cleanWrite := MemoryCellClocks.nonAtomicWriteDetect
    (MemoryCellClocks.new z i0) (threadWith i0 t1) i0 .Retag
  IO.println s!"cell:non-atomic-write:{codeResult cleanWrite.result}:{codeNaWriteType cleanWrite.cell.writeType}:{packedAt cleanWrite.cell.read i0}:{atomicSizeCode cleanWrite.cell}"

  let published := MemoryCellClocks.storeRelease
    (MemoryCellClocks.new z i0) (threadWith i0 t1) i0 fourBytes
  IO.println s!"cell:store-release:{codeResult published.result}:{atomicSyncClockAt published.cell i0}"

  let loaded := MemoryCellClocks.loadAcquire
    published.cell (threadWith i1 t1) i1 fourBytes
  IO.println s!"cell:load-acquire:{codeResult loaded.result}:{packedAt loaded.thread.clock i0}"

  let relaxedLoaded := MemoryCellClocks.loadRelaxed
    published.cell (threadWith i1 t1) i1 fourBytes
  IO.println s!"cell:load-relaxed:{codeResult relaxedLoaded.result}:{packedAt relaxedLoaded.thread.fenceAcquire i0}"

  let releaseFenceThread :=
    { (threadWith i1 t1) with fenceRelease := clockAt i2 t2 }
  let relaxedStored := MemoryCellClocks.storeRelaxed
    published.cell releaseFenceThread i1 fourBytes
  IO.println s!"cell:store-relaxed:{codeResult relaxedStored.result}:{atomicSyncClockAt relaxedStored.cell i0}:{atomicSyncClockAt relaxedStored.cell i2}"

  let rmwReleased := MemoryCellClocks.rmwRelease
    published.cell (threadWith i2 t2) i2 fourBytes
  IO.println s!"cell:rmw-release:{codeResult rmwReleased.result}:{atomicSyncClockAt rmwReleased.cell i0}:{atomicSyncClockAt rmwReleased.cell i2}"

  let rmwRelaxedThread :=
    { (threadWith i2 t1) with fenceRelease := clockAt i2 t2 }
  let rmwRelaxed := MemoryCellClocks.rmwRelaxed
    published.cell rmwRelaxedThread i2 fourBytes
  IO.println s!"cell:rmw-relaxed:{codeResult rmwRelaxed.result}:{atomicSyncClockAt rmwRelaxed.cell i0}:{atomicSyncClockAt rmwRelaxed.cell i2}"

  let alloc := VClockAlloc.newAllocation twoBytes z i0
  let range : AccessRange := { start := zeroOffset, size := twoBytes }
  let rangeRead := VClockAlloc.readNonAtomic alloc range (threadWith i0 t1) i0 .Retag
  let cell0 := rangeRead.allocation.cellAt 0
  let cell1 := rangeRead.allocation.cellAt 1
  IO.println s!"alloc:two-byte-retag:{codeResult rangeRead.result}:{match cell0 with | .ok cell => codeNaReadType (cell.read.index i0).readType | .error _ => "missing"}:{match cell1 with | .ok cell => codeNaReadType (cell.read.index i0).readType | .error _ => "missing"}"

  let atomicAlloc := VClockAlloc.newAllocation fourBytes z i0
  let atomicRange : AccessRange := { start := zeroOffset, size := fourBytes }
  let publishedRange := VClockAlloc.atomicStore atomicAlloc atomicRange
    (threadWith i0 t1) i0 fourBytes .Release
  let loadedRange := VClockAlloc.atomicLoad publishedRange.allocation atomicRange
    (threadWith i1 t1) i1 fourBytes .Acquire
  IO.println s!"alloc:atomic-range-load:{codeResult loadedRange.result}:{packedAt loadedRange.thread.clock i0}:{packedAt loadedRange.thread.clock i1}"

  let rmwThread := { ThreadClockSet.default with
    clock := VClock.fromTimestamps [t1, t1, t2] }
  let rmwRange := VClockAlloc.atomicRmw loadedRange.allocation atomicRange
    rmwThread i2 fourBytes .AcqRel
  IO.println s!"alloc:atomic-range-rmw:{codeResult rmwRange.result}:{packedAt rmwRange.thread.clock i0}:{packedAt rmwRange.thread.clock i1}:{packedAt rmwRange.thread.clock i2}"
