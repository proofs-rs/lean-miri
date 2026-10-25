import Miri.Concurrency.LocalRace
open Miri.Concurrency
open Miri.Concurrency.LocalRace

def index : VectorIdx := VectorIdx.ofU32 0 (by decide)
def stamp (time : Nat) : IO VTimestamp :=
  match VTimestamp.ofTime time with
  | .ok value => pure value
  | .error _ => throw (IO.userError "time")
def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
def global (detect : Bool) (timestamp : VTimestamp) : GlobalState :=
  { GlobalState.initial false false with
    multiThreaded := detect
    vectorClocks := [{ clock := VClock.newWithIndex index timestamp }] }
def printLocal (label : String) (frame : FrameState) : IO Unit := do
  let clocks := frame.get 1
  let kind := match clocks.writeType with | .Allocate => "a" | .Write => "w" | .Deallocate => "d" | .Retag => "t"
  IO.println s!"{label} {frame.localClocks.size} {clocks.write.packedValue} {kind} {clocks.read.packedValue}"
def main : IO Unit := do
  let threads := ThreadManager.initial false
  for detect in [false, true] do
    for live in [false, true] do
      let t ← stamp 3
      let g := global detect t
      let read := localRead {} g threads 1
      let .ok () := read.outcome | throw (IO.userError "read")
      printLocal s!"R {detect} {live}" read.frame
      let written := localWrite read.frame (global detect (← stamp 5)) threads 1 live
      let .ok () := written.outcome | throw (IO.userError "write")
      printLocal s!"W {detect} {live}" written.frame
      let alloc := VClockAlloc.newAllocation (ByteSize.ofU64 2 (by decide)) (← stamp 9) index
      let moved := localMovedToMemory written.frame (global detect (← stamp 9)) threads 1 alloc
      let .ok () := moved.outcome | throw (IO.userError "move")
      let .ok cell := moved.allocation.cellAt 0 | throw (IO.userError "cell")
      let kind := match cell.writeType with | .Allocate => "a" | .Write => "w" | .Deallocate => "d" | .Retag => "t"
      IO.println s!"M {detect} {live} {moved.frame.localClocks.size} {cell.write.2.packedValue} {kind} {(cell.read.index index).packedValue}"
  -- Transfer a historical write before a second thread's observation snapshot.
  let old ← stamp 2
  let new ← stamp 9
  let writtenLocal :=  localWrite {} (global true old) threads 1 false
  let allocation := VClockAlloc.newAllocation (ByteSize.ofU64 1 (by decide)) new index
  let moved := localMovedToMemory writtenLocal.frame (global true new) threads 1 allocation
  let otherIndex := VectorIdx.ofU32 1 (by decide)
  let otherClock := (VClock.newWithIndex index old).join (VClock.newWithIndex otherIndex (← stamp 3))
  let read := moved.allocation.readNonAtomic ⟨ByteSize.ofU64 0 (by decide), ByteSize.ofU64 1 (by decide)⟩
    { clock := otherClock } otherIndex .Read
  check (read.result == .ok) "historical pre-spawn write remains synchronized after materialization"
  let lateLocal := localWrite {} (global true (← stamp 4)) threads 1 false
  let lateMoved := localMovedToMemory lateLocal.frame (global true new) threads 1 allocation
  let raced := lateMoved.allocation.readNonAtomic ⟨ByteSize.ofU64 0 (by decide), ByteSize.ofU64 1 (by decide)⟩
    { clock := otherClock } otherIndex .Read
  check (raced.result != .ok) "post-spawn local write survives materialization as memory race"
  let readLocal := localRead writtenLocal.frame (global true (← stamp 4)) threads 1
  let readMoved := localMovedToMemory readLocal.frame (global true new) threads 1 allocation
  let raced := readMoved.allocation.writeNonAtomic ⟨ByteSize.ofU64 0 (by decide), ByteSize.ofU64 1 (by decide)⟩
    { clock := otherClock } otherIndex .Write
  check (raced.result != .ok) "historical local read survives materialization as memory race"
  let first := localWrite {} (global true (← stamp 5)) threads 1 false
  let badCell : MemoryCellClocks := .new (← stamp 9) otherIndex
  let .ok mixed := (VClockAlloc.newAllocation (ByteSize.ofU64 2 (by decide)) new index).setCell 1 badCell
    | throw (IO.userError "mixed allocation")
  let failed := localMovedToMemory first.frame (global true new) threads 1 mixed
  check (!failed.outcome.isOk && failed.frame.localClocks.isEmpty) "map removal precedes failed writer assertion"
  let .ok firstCell := failed.allocation.cellAt 0 | throw (IO.userError "first byte")
  let .ok lastCell := failed.allocation.cellAt 1 | throw (IO.userError "last byte")
  check (firstCell.write.2.time == 5 && lastCell.write.1 == otherIndex) "partial materialization retains previous byte transfer"
  let disabled := localMovedToMemory first.frame (global false new) threads 1 mixed
  check (disabled.outcome.isOk && disabled.frame.localClocks.size == 1) "race guard skips map removal and assertions"
  let retagStamp := (← stamp 3).setReadType .Retag
  let read := localRead {} (global true retagStamp) threads 1
  check ((read.frame.get 1).read.readType == .Read) "local read clears packed retag bit"
  let suppressed := { global true new with ongoingActionDataRaceFree := true }
  let skipped := localWrite first.frame suppressed threads 1 true
  check ((skipped.frame.get 1).write.time == 5) "ongoing data-race-free action suppresses local timestamp replacement"
