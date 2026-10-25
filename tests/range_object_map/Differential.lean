import Miri.DataStructures.RangeObjectMap

open Miri.ABI Miri.Memory Miri.DataStructures

private def size (value : Nat) : Size := Size.ofBytes (UInt64.ofNat value)
private def range (start length : Nat) : AllocRange := allocRange (size start) (size length)

private def showValues (map : RangeObjectMap Nat) : String :=
  String.intercalate "," (map.iter.toList.map toString)

private def showSearch (result : Except RangeObjectMapError OffsetSearch) : String :=
  match result with
  | .error _ => "P"
  | .ok (.found position) => s!"F{position}"
  | .ok (.insertionPoint position) => s!"I{position}"

private def showAccess (result : Except RangeObjectMapError AccessType) : String :=
  match result with
  | .error _ => "P"
  | .ok (.perfectlyOverlapping position) => s!"P{position}"
  | .ok (.empty position) => s!"E{position}"
  | .ok (.imperfectlyOverlapping positions) =>
      s!"I{positions.start}:{positions.stop}"

private def emitAccess (tag : String) (map : RangeObjectMap Nat)
    (start length : Nat) : IO Unit := do
  IO.println s!"A {tag} {showAccess (map.accessType (range start length))}"

private def emitSearch (tag : String) (map : RangeObjectMap Nat) (offset : Nat) : IO Unit := do
  IO.println s!"Q {tag} {showSearch (map.findOffset (size offset))}"

private def emitValues (tag : String) (map : RangeObjectMap Nat) : IO Unit := do
  IO.println s!"V {tag} {showValues map}"

private def emitInsert (tag : String) (map : RangeObjectMap Nat)
    (position start length data : Nat) : IO (RangeObjectMap Nat) := do
  let result := map.insertAtPos position (range start length) data
  let outcome := match result.outcome with | .ok _ => "O" | .error _ => "P"
  IO.println s!"M {tag} {outcome} {showValues result.state}"
  return result.state

private def emitRemovePos (tag : String) (map : RangeObjectMap Nat)
    (position : Nat) : IO (RangeObjectMap Nat) := do
  let result := map.removeFromPos position
  let outcome := match result.outcome with | .ok _ => "O" | .error _ => "P"
  IO.println s!"M {tag} {outcome} {showValues result.state}"
  return result.state

private def emitDrain (tag : String) (map : RangeObjectMap Nat)
    (start stop : Nat) : IO (RangeObjectMap Nat) := do
  let result := map.removePosRange start stop
  let outcome := match result.outcome with | .ok _ => "O" | .error _ => "P"
  IO.println s!"M {tag} {outcome} {showValues result.state}"
  return result.state

private def showIndex (result : Except RangeObjectMapError Nat) : String :=
  match result with | .ok value => toString value | .error _ => "P"

def main : IO Unit := do
  let mut empty : RangeObjectMap Nat := .new
  emitSearch "empty-left" empty 3
  emitAccess "empty-access" empty 0 4
  emitAccess "empty-zero-at-zero" empty 0 0
  empty ← emitInsert "first" empty 0 4 4 1
  emitSearch "before-first" empty 3
  emitSearch "at-first" empty 4
  emitSearch "at-end-first" empty 8
  emitAccess "left-straddle" empty 2 4
  emitAccess "right-straddle" empty 6 4
  emitAccess "full-straddle" empty 2 8
  emitAccess "exact-first" empty 4 4
  emitAccess "touch-after-first" empty 8 4
  emitAccess "zero-inside-first" empty 4 0

  empty ← emitInsert "second" empty 1 10 2 2
  emitAccess "two-object-straddle" empty 6 8
  emitSearch "gap" empty 9
  emitSearch "second-start" empty 10
  emitAccess "touch-gap" empty 8 2
  emitValues "two-values" empty

  let mut badNext : RangeObjectMap Nat := .new
  badNext ← emitInsert "bad-next-seed" badNext 0 4 4 1
  badNext ← emitInsert "bad-next" badNext 0 1 4 2
  emitValues "bad-next-state" badNext
  emitAccess "bad-next-class" badNext 1 4

  let mut badPrev : RangeObjectMap Nat := .new
  badPrev ← emitInsert "bad-prev-seed" badPrev 0 1 4 1
  badPrev ← emitInsert "bad-prev" badPrev 1 2 1 2
  emitValues "bad-prev-state" badPrev

  let mut edits : RangeObjectMap Nat := .new
  edits ← emitInsert "edit-a" edits 0 0 1 3
  edits ← emitInsert "edit-b" edits 1 2 1 4
  IO.println s!"G read-valid {showIndex (edits.index 0)}"
  IO.println s!"G read-invalid {showIndex (edits.index 8)}"
  let set := edits.setAtPos 0 7
  edits := set.state
  IO.println s!"M set-valid {match set.outcome with | .ok _ => "O" | .error _ => "P"} {showValues edits}"
  let set := edits.setAtPos 8 9
  edits := set.state
  IO.println s!"M set-invalid {match set.outcome with | .ok _ => "O" | .error _ => "P"} {showValues edits}"
  edits ← emitRemovePos "remove-valid" edits 0
  edits ← emitRemovePos "remove-invalid" edits 8
  edits ← emitDrain "drain-valid" edits 0 1
  edits ← emitDrain "drain-empty-at-end" edits 0 0
  edits ← emitInsert "edit-c" edits 0 5 1 5
  edits ← emitDrain "drain-reversed" edits 2 1
  edits ← emitDrain "drain-oob" edits 0 2
  edits ← emitInsert "insert-oob" edits 8 7 1 9

  let mut edge : RangeObjectMap Nat := .new
  edge ← emitInsert "edge-seed" edge 0 18446744073709551614 1 1
  emitSearch "edge-max" edge 18446744073709551615
  emitAccess "overflow-access" edge 18446744073709551615 1

  let mut overflowEntry : RangeObjectMap Nat := .new
  overflowEntry ← emitInsert "overflow-tail-insert" overflowEntry 0 18446744073709551615 1 9
  emitSearch "overflow-entry-search" overflowEntry 18446744073709551615

  let mut multi : RangeObjectMap Nat := .new
  multi ← emitInsert "multi-0" multi 0 2 2 10
  multi ← emitInsert "multi-1" multi 1 6 2 11
  multi ← emitInsert "multi-2" multi 2 10 2 12
  multi ← emitInsert "multi-3" multi 3 14 2 13
  for offset in [0:18] do
    emitSearch s!"multi-{offset}" multi offset
  emitAccess "multi-all" multi 0 18
  emitAccess "multi-two-middle" multi 4 10
  emitAccess "multi-empty-one" multi 4 2
  emitAccess "multi-straddle-two" multi 3 4
  emitAccess "multi-empty-two" multi 8 2
  emitAccess "multi-end-in-three" multi 8 3
  emitAccess "multi-empty-before" multi 0 2
  emitAccess "multi-empty-after" multi 16 2

theorem empty_map_is_well_formed :
    RangeObjectMap.WellFormed (RangeObjectMap.new : RangeObjectMap Nat) := by
  intro i j hi hj hij
  simp [RangeObjectMap.new] at hi

theorem empty_positive_range_is_empty :
    RangeObjectMap.accessType (RangeObjectMap.new : RangeObjectMap Nat)
      (range 0 4) = .ok (.empty 0) := by
  native_decide
