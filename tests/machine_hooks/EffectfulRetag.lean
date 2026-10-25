import Miri.TreeBorrows.RetagPipelineEffectful
import Miri.Interpreter.MachineHooks
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.RetagPolicy
open Miri.Concurrency Miri.Interpreter

namespace EffectfulRetagTests

def id : AllocId := ⟨1, by decide⟩
def parent : BorTag := ⟨1, by decide⟩
def child : BorTag := ⟨2, by decide⟩
def zeroIndex : VectorIdx := .ofU32 0 (by decide)
def oneIndex : VectorIdx := .ofU32 1 (by decide)
def time (n : Nat) : IO VTimestamp :=
  match VTimestamp.ofTime n with | .ok t => pure t | .error _ => throw (IO.userError "timestamp")
def check (yes : Bool) (message : String) : IO Unit :=
  unless yes do throw (IO.userError message)
def memory : IO (MemoryState Provenance BorrowTree Unit) := do
  let .ok allocation := Allocation.fromBytes (Prov := Provenance) #[7, 8] Align.ONE .Mut
    | throw (IO.userError "allocation")
  let memory := MemoryState.setIssuedIds
    (MemoryState.empty : MemoryState Provenance BorrowTree Unit) #[id]
  return {memory with
    live := #[(id, ⟨.stack, allocation.withExtra (BorrowTree.new parent (Size.ofBytes 2))⟩)]}
def request : RetagPipeline.Request := {
  typeShape := .reference, typeFacts := ⟨true, true, false⟩, referenceKind := .Mutable
  mode := .Default, config := ⟨false, false⟩, layoutSize := Size.ofBytes 2
  originalProvenance := some (.concrete id parent)
  pointeeIsFreeze := false, preciseInteriorMut := true
  hooks := {
    placeConversion := .ok (), sizeAndAlignOfValue := .ok none, pointerAccess := .ok ()
    allocationResolution := some ⟨id, Size.ZERO, .concrete parent⟩
    creationLog := .ok ()
    freezeVisitor := .ok ⟨#[⟨⟨0, 1⟩, true⟩, ⟨⟨1, 2⟩, false⟩]⟩
    allocationExtra := .ok ()
    -- Deliberately wrong legacy fixture outcomes: the effectful engine ignores these.
    dataRace := some #[.error "legacy precomputed outcomes must not be consumed"] } }

structure External where
  machine : MachineHooks.MachineState Unit (List String)
  observed : Array (AccessKind × AllocRange × Bool × UInt64) := #[]

def effectHooks : RetagPipeline.Effectful.Hooks Unit External StepError := {
  dataRace := some fun core external allocId kind range => Id.run do
    let childAbsent := (core.memory.live[0]?.bind fun entry => entry.2.allocation.extra.indexOfTag child).isNone
    let observed := external.observed.push (kind, range, childAbsent, core.global.nextPointerTag.value)
    let (machine, outcome) := MachineHooks.memoryRaceAccess external.machine allocId range
      (if kind == .Write then some .Retag else none) .Retag
    return ⟨{ external with machine, observed }, outcome⟩ }

def makeExternal (memory : MemoryState Provenance BorrowTree Unit) (raceSecond : Bool) : IO External := do
  let old ← time 1
  let mut allocation := VClockAlloc.newAllocation (ByteSize.ofU64 2 (by decide)) old zeroIndex
  if raceSecond then
    let .ok updated := allocation.setCell 1 (.new (← time 5) oneIndex)
      | throw (IO.userError "allocation")
    allocation := updated
  let global := { Miri.Concurrency.GlobalState.initial false false with
    multiThreaded := true
    vectorClocks := [{ clock := VClock.newWithIndex zeroIndex (← time 3) },
      { clock := VClock.newWithIndex oneIndex (← time 5) }]
    vectorInfo := [ThreadId.MAIN_THREAD, ThreadId.ofU32 1 (by decide)]
    threadInfo := [⟨some zeroIndex, none⟩, ⟨some oneIndex, none⟩] }
  let threads := { ThreadManager.initial false with
    threads := [ThreadRecord.initial none none, ThreadRecord.initial none none] }
  return ⟨⟨memory, none, some global, threads, #[(id, allocation)], #[], []⟩, #[]⟩

end EffectfulRetagTests
open EffectfulRetagTests

def main : IO Unit := do
  let memory ← memory
  let core : RetagPipeline.MachineState Unit := ⟨memory,
    { Miri.TreeBorrows.GlobalState.new with nextPointerTag := child }, {}⟩
  for write in [false, true] do
    for readonly in [false, true] do
      for racy in [false, true] do
        let memory := if readonly then { memory with live := memory.live.map fun (allocationId, entry) =>
          (allocationId, { entry with allocation := entry.allocation.withMutability .Not }) } else memory
        let core := { core with memory }
        let request := if write then { request with
          mode := .FnEntry
          config := ⟨true, false⟩
          preciseInteriorMut := false } else request
        let external ← makeExternal memory racy
        let result := RetagPipeline.Effectful.retagPointerValue core request external effectHooks
        let failedReadonly := write && readonly
        check (result.external.observed.size == if failedReadonly then 0 else if write then 1 else 2)
          "race leaf follows each source parent permission segment"
        check (result.external.observed.all fun (_, _, absent, next) => absent && next == 3)
          "callback observes allocated tag and no child yet"
        let some (_, allocation) := result.external.machine.raceAllocations[0]? | throw (IO.userError "clock allocation")
        let .ok firstCell := allocation.cellAt 0 | throw (IO.userError "first cell")
        let .ok secondCell := allocation.cellAt 1 | throw (IO.userError "second cell")
        let some (_, entry) := result.state.memory.live[0]? | throw (IO.userError "tree allocation")
        check ((entry.allocation.extra.indexOfTag child).isSome == !(racy || failedReadonly))
          "child inserted only after all TB and race stages succeed"
        if failedReadonly then
          check (match result.outcome with | .error (.core (.writeToReadOnly _)) => true | _ => false)
            "read-only write rejected before parent/race stage"
        else if racy then
          check (match result.outcome with | .error (.hook (.undefinedBehavior "DataRace")) => true | _ => false)
            "actual two-thread race escapes with typed hook failure"
        else check result.outcome.isOk "stateful retag ignores legacy precomputed outcomes"
        if write then
          check (result.state.global.protectedTags.get child == some .StrongProtector &&
            result.state.frame.protectedTags.contains (id, child)) "protector registration survives failure prefix"
          if !readonly then
            check (firstCell.write.2.time == 3 && firstCell.writeType == .Retag)
              "partial retag write updates actual clocks before second-byte race"
        else check ((firstCell.read.index zeroIndex).time == 3 &&
          (firstCell.read.index zeroIndex).readType == .Retag) "read retag kind retained in memory clocks"
        let trace := result.events.toList.filterMap fun event => match event with
          | .parentTreeAccess _ range => some s!"T{range.start}"
          | .dataRaceAccess kind range => some s!"{if kind == .Read then "R" else "W"}{range.start}"
          | .childInserted _ => some "C"
          | _ => none
        IO.println s!"E {write} {readonly} {racy} {result.outcome.isOk} {(entry.allocation.extra.indexOfTag child).isSome} {(firstCell.read.index zeroIndex).packedValue} {(secondCell.read.index zeroIndex).packedValue} {firstCell.write.2.packedValue} {secondCell.write.2.packedValue} {firstCell.writeType == .Retag} {secondCell.writeType == .Retag} {String.intercalate "," trace}"
  let external ← makeExternal memory false
  let sourceNoModel : RetagPipeline.Effectful.Hooks Unit External StepError := ⟨none⟩
  let disabled := { external with machine := { external.machine with dataRace := none, raceAllocations := #[] } }
  let result := RetagPipeline.Effectful.retagPointerValue core request disabled sourceNoModel
  check (result.outcome.isOk && result.external.observed.isEmpty) "no vector-clock model calls no race hook"
  let raw := RetagPipeline.Effectful.retagPointerValue core
    { request with typeShape := .rawPointer, mode := .Raw } external effectHooks
  check (raw.outcome.isOk && raw.external.observed.isEmpty && raw.events.isEmpty)
    "source raw-pointer retag has no race or pointer operation"
  let disabledRetag := RetagPipeline.Effectful.retagPointerValue core
    { request with mode := .None } external effectHooks
  check (disabledRetag.outcome.isOk && disabledRetag.state.global.nextPointerTag == child && disabledRetag.external.observed.isEmpty)
    "source None mode returns before tag or race operations"
  let zero := RetagPipeline.Effectful.retagPointerValue core
    { request with layoutSize := Size.ZERO, preciseInteriorMut := false } external effectHooks
  let some (_, zeroAllocation) := zero.state.memory.live[0]? | throw (IO.userError "zero allocation")
  check (zero.outcome.isOk && zero.external.observed.isEmpty && (zeroAllocation.allocation.extra.indexOfTag child).isSome)
    "zero-byte reborrow inserts lazy child without any memory race stage"
