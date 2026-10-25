import Miri.DataStructures.DedupRangeMap

open Miri.ABI Miri.DataStructures

private def size (value : Nat) : Size := Size.ofBytes (UInt64.ofNat value)

private def showSegments (segments : Array (RangeMapSegment Int)) : String :=
  String.intercalate "," (segments.toList.map fun segment =>
    s!"{segment.range.start}:{segment.range.stop}={segment.data}")

private def showMap (map : DedupRangeMap Int) : String := showSegments map.entries

private def emitIter (tag : String) (map : DedupRangeMap Int) (offset len : Nat) : IO Unit := do
  let result := map.iter (size offset) (size len)
  let output := match result with
    | .error _ => "P"
    | .ok segments => showSegments segments
  IO.println s!"R {tag} {output}"

private def emitMutSet (tag : String) (map : DedupRangeMap Int)
    (offset len value : Nat) : IO (DedupRangeMap Int) := do
  let result := map.modifyRange (size offset) (size len) (fun _ _ => Int.ofNat value)
  let status := match result.outcome with | .ok _ => "O" | .error _ => "P"
  let selected := if status == "O" then showSegments result.segments else "P"
  IO.println s!"M {tag} {status} {selected} {showMap result.state}"
  return result.state

private def emitMutBelow (tag : String) (map : DedupRangeMap Int)
    (offset len : Nat) (threshold : Int) (value : Int) : IO (DedupRangeMap Int) := do
  let result := map.modifyRange (size offset) (size len)
      (fun _ data => if data < threshold then value else data)
  let status := match result.outcome with | .ok _ => "O" | .error _ => "P"
  let selected := if status == "O" then showSegments result.segments else "P"
  IO.println s!"M {tag} {status} {selected} {showMap result.state}"
  return result.state

private def emitMutNoop (tag : String) (map : DedupRangeMap Int)
    (offset len : Nat) : IO (DedupRangeMap Int) := do
  let result := map.modifyRange (size offset) (size len) (fun _ data => data)
  let status := match result.outcome with | .ok _ => "O" | .error _ => "P"
  let selected := if status == "O" then showSegments result.segments else "P"
  IO.println s!"M {tag} {status} {selected} {showMap result.state}"
  return result.state

private def emitMerge (tag : String) (map : DedupRangeMap Int) : IO (DedupRangeMap Int) := do
  let result := map.mergeAdjacentThorough
  let status := match result.outcome with | .ok _ => "O" | .error _ => "P"
  IO.println s!"M {tag} {status} {showMap result.state}"
  return result.state

def main : IO Unit := do
  let mut basic : DedupRangeMap Int := .new (size 20) (-1)
  IO.println s!"S initial {basic.size.bytes}"
  emitIter "initial-overlap" basic 10 1
  emitIter "initial-empty" basic 10 0
  emitIter "initial-at-end" basic 20 0
  emitIter "initial-past-end-zero" basic 21 0
  emitIter "initial-past-end" basic 11 11
  basic ← emitMutSet "basic-one" basic 10 1 42
  emitIter "basic-values" basic 10 1
  basic ← emitMutSet "zero-in-middle" basic 10 0 19
  basic ← emitMutSet "zero-at-map-end" basic 20 0 19

  let mut gaps : DedupRangeMap Int := .new (size 20) (-1)
  gaps ← emitMutSet "gap-a" gaps 11 1 42
  gaps ← emitMutSet "gap-b" gaps 15 1 43
  gaps ← emitMutBelow "gap-fill" gaps 10 10 42 23
  gaps ← emitMutSet "gap-tail" gaps 15 5 19
  emitIter "two-19s" gaps 15 2
  gaps ← emitMutNoop "gap-nop-merges" gaps 15 5
  gaps ← emitMerge "thorough-merge" gaps

  let mut empty : DedupRangeMap Int := .new (size 0) (-1)
  IO.println s!"S empty {empty.size.bytes}"
  emitIter "empty-zero" empty 0 0
  emitIter "empty-past-zero" empty 1 0
  empty ← emitMutSet "empty-mut-zero" empty 999 0 3
  empty ← emitMutSet "empty-mut-nonzero" empty 0 1 4

  let mut outOfRange : DedupRangeMap Int := .new (size 20) (-1)
  outOfRange ← emitMutSet "mut-out-of-range" outOfRange 11 11 7
  emitIter "after-failed-mut" outOfRange 10 10
  outOfRange ← emitMutSet "mut-start-out-of-range" outOfRange 20 1 8

  let mut maxSize : DedupRangeMap Int := .new (size 18446744073709551615) 5
  emitIter "u64-end-overflow" maxSize 18446744073709551614 2
  maxSize ← emitMutSet "u64-mut-overflow" maxSize 18446744073709551614 2 6
  IO.println s!"V max-after-error {showMap maxSize}"

  let cloneMap : DedupRangeMap Int := .new (size 10) 1
  let cloned := cloneMap.modifyRangeWithClone (size 3) (size 2)
      (fun value => value + 100) (fun _ value => value)
  let cloneStatus := match cloned.outcome with | .ok _ => "O" | .error _ => "P"
  let cloneSelected := if cloneStatus == "O" then showSegments cloned.segments else "P"
  IO.println s!"M clone-on-split {cloneStatus} {cloneSelected} {showMap cloned.state}"

theorem empty_map_is_well_formed :
    (DedupRangeMap.new (size 0) (0 : Int)).WellFormed := by
  exact DedupRangeMap.new_wellFormed _ _

theorem new_map_reports_its_size {α : Type} (n : UInt64) (value : α) :
    (DedupRangeMap.new (Size.ofBytes n) value).size = Size.ofBytes n := by
  by_cases h : n = 0
  · simp [DedupRangeMap.size, DedupRangeMap.new, Size.ZERO, Size.ofBytes, h]
  · simp [DedupRangeMap.size, DedupRangeMap.new, Size.ofBytes, h]
