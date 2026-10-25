import Miri.Concurrency.DataRace

open Miri.Concurrency

private def ix0 : VectorIdx := .ofU32 0 (by decide)
private def ix1 : VectorIdx := .ofU32 1 (by decide)

private def size (bytes : Fin 5) : ByteSize := .ofU64 bytes.val (by omega)

private def timestamp (time : Fin 4) : VTimestamp :=
  VTimestamp.ofPacked (2 * time.val) (by omega)

private def clock (left right : Fin 4) : VClock :=
  VClock.fromTimestamps [timestamp left, timestamp right]

private def code (result : Except DataRaceResult VClock) : String :=
  match result with
  | .error _ => "error"
  | .ok value =>
    s!"{(value.index ix0).time},{(value.index ix1).time}"

private def stateWithSyncClocks : Except DataRaceResult VClockAlloc := do
  let initial := VClockAlloc.newAllocation (size ⟨4, by decide⟩) VTimestamp.ZERO ix0
  let leftCell := MemoryCellClocks.new VTimestamp.ZERO ix0
  let leftCell := { leftCell with atomicOps := some {
    syncVector := clock ⟨2, by decide⟩ ⟨0, by decide⟩, size := some (size ⟨2, by decide⟩) } }
  let rightCell := MemoryCellClocks.new VTimestamp.ZERO ix0
  let rightCell := { rightCell with atomicOps := some {
    syncVector := clock ⟨0, by decide⟩ ⟨3, by decide⟩, size := some (size ⟨1, by decide⟩) } }
  let afterLeft ← initial.setCell 0 leftCell
  afterLeft.setCell 1 rightCell

def main : IO Unit := do
  match stateWithSyncClocks with
  | .error _ => IO.println "setup:error"
  | .ok state => do
    IO.println s!"sync:join:{code (state.syncClock ⟨size ⟨0, by decide⟩, size ⟨2, by decide⟩⟩)}"
    IO.println s!"sync:empty:{code (state.syncClock ⟨size ⟨4, by decide⟩, size ⟨0, by decide⟩⟩)}"
    IO.println s!"sync:bounds:{code (state.syncClock ⟨size ⟨3, by decide⟩, size ⟨2, by decide⟩⟩)}"
