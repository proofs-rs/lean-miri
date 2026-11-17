import duplicate_prefix.GeneralRangeMapMerge
namespace DuplicatePrefix.GeneralRangeMapScan
open Miri Miri.ABI Miri.DataStructures
open DuplicatePrefix.RangeMapNonempty GeneralRangeMapMerge
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
abbrev State (α : Type) := DedupRangeMap α × Nat × Nat × Nat × Bool × Option DedupRangeMapError

def step [DecidableEq α] (finish : UInt64) (_ : Unit) (state : State α) : Id (ForInStep (State α)) := do
  let mut current := state.1
  let mut equalSinceIndex := state.2.1
  let mut successfulMergeCount := state.2.2.1
  let mut endIndex := state.2.2.2.1
  let mut done := state.2.2.2.2.1
  let mut failure := state.2.2.2.2.2
  if !done && failure.isNone then
    match range_segment_at current.entries endIndex with
    | none => failure := some (.indexOutOfBounds endIndex current.entries.size)
    | some segment =>
        let complete := segment.range.stop ≥ finish
        endIndex := endIndex+1
        if !complete && endIndex ≥ current.entries.size then
          failure := some (.iterationPastMap finish current.size.bytes)
        else
          if successfulMergeCount > 0 then
            let shouldMerge ←
              if complete then pure true
              else
                match range_segment_at current.entries endIndex with
                | none =>
                    failure := some (.indexOutOfBounds endIndex current.entries.size)
                    pure false
                | some next =>
                    match range_segment_at current.entries equalSinceIndex with
                    | none =>
                        failure := some (.indexOutOfBounds equalSinceIndex current.entries.size)
                        pure false
                    | some firstEqual => pure (next.data != firstEqual.data)
            if shouldMerge && failure.isNone then
              let removedCount := endIndex-equalSinceIndex-1
              if removedCount > 0 then
                match range_merge_run current.entries equalSinceIndex endIndex with
                | .error error => failure := some error
                | .ok entries =>
                    current := {current with entries}
                    endIndex := endIndex-removedCount
                    successfulMergeCount := successfulMergeCount+removedCount
              else
                successfulMergeCount := successfulMergeCount-1
              equalSinceIndex := endIndex
          if complete && failure.isNone then done := true
    pure (.yield (current,equalSinceIndex,successfulMergeCount,endIndex,done,failure))
  else pure (.done (current,equalSinceIndex,successfulMergeCount,endIndex,done,failure))

end DuplicatePrefix.GeneralRangeMapScan

open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.GeneralRangeMapScan.step) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved range scan factor {dependency}"
