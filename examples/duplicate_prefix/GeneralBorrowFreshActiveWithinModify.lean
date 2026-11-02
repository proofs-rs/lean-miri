import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
namespace DuplicatePrefix.GeneralBorrowFreshActiveWithinModify
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshActiveWithin
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem replace_write (map : DedupRangeMap LocationTree) (position : Nat)
    (valid : position < map.entries.size) (location : LocationTree) (anchor : UniIndex) (lower upper : UInt64)
    (active : Profile map anchor .Write lower upper)
    (inside : lower.toNat ≤ map.entries[position].range.start.toNat ∧ map.entries[position].range.stop.toNat ≤ upper.toNat) :
    Profile (replaced map position valid location) anchor .Write lower upper := by
  intro point value atPoint state stored accessed kind associated
  obtain ⟨query,bounded,startPoint,pointStop,dataEq⟩ := atPoint
  have oldBound : query < map.entries.size := by simpa only [replaced_length] using bounded
  rw [replaced_range map position valid location query oldBound] at startPoint pointStop
  by_cases same : position = query
  · subst query
    exact ⟨Nat.le_trans inside.1 startPoint,Nat.lt_of_lt_of_le pointStop inside.2,by intro h;cases h⟩
  · have dataSame : (replaced map position valid location).entries[query].data = map.entries[query].data := by
      simp [replaced,Array.getElem_set,same]
    rw [dataSame] at dataEq
    exact active point value ⟨query,oldBound,startPoint,pointStop,dataEq⟩ state stored accessed kind associated

/-- The actual modifier preserves an older mutable anchor's bytewise activity
for any callback whose requested interval lies inside that anchor's slice.
No callback, modifier-success or post-state ownership premise is supplied. -/
theorem modified (map : DedupRangeMap LocationTree) (anchor : UniIndex) (offset len : Size)
    (modify : ByteRange → LocationTree → LocationTree) (lower upper : UInt64)
    (well : map.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat) (requestUpper : (offset.bytes+len.bytes).toNat ≤ upper.toNat)
    (active : Profile map anchor .Write lower upper) :
    Profile (map.modifyRange offset len modify).state anchor .Write lower upper := by
  let prepared := map.iterMut offset len
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut map offset len well bounds
  have good := preparedData.1
  have preparedActive := refines map prepared.state preparedData.2.1 anchor .Write lower upper active
  let property := fun current : DedupRangeMap LocationTree =>
    current.entries.map (·.range) = prepared.state.entries.map (·.range) ∧ Profile current anchor .Write lower upper
  have fold : ∀ (items : List Nat), (∀ position ∈ items, position ∈ prepared.positions.toList) →
      ∀ current, property current →
        property (items.foldl (fun current position => GeneralBorrowFreshModify.atPosition current position modify) current) := by
    intro items
    induction items with
    | nil => intro _ current maintained;exact maintained
    | cons position rest ih =>
      intro included current maintained
      rcases maintained with ⟨ranges,currentActive⟩
      have sizeEq : current.entries.size = prepared.state.entries.size := by
        have known := congrArg Array.size ranges
        simpa only [Array.size_map] using known
      obtain ⟨cursor,cursorBound,same⟩ := Array.mem_iff_getElem.mp (Array.mem_def.mpr (included position (by simp)))
      have known := good.selected cursor cursorBound
      have positionBound : position < prepared.state.entries.size := by
        have valid := known.choose
        change prepared.positions[cursor] < prepared.state.entries.size at valid
        simpa only [same] using valid
      have currentBound : position < current.entries.size := by rw [sizeEq];exact positionBound
      have segmentBound : cursor < prepared.segments.size := by rw [←good.lengths];exact cursorBound
      have selected : prepared.segments[cursor] = prepared.state.entries[position] := by
        have selected := known.choose_spec
        change prepared.segments[cursor] = prepared.state.entries[prepared.positions[cursor]] at selected
        simpa only [same] using selected
      have rangeSame : current.entries[position].range = prepared.segments[cursor].range := by
        have range := congrArg (fun rows => rows[position]?) ranges
        simp only [Array.getElem?_map,
          Array.getElem?_eq_getElem (xs := current.entries) (i := position) currentBound,
          Array.getElem?_eq_getElem (xs := prepared.state.entries) (i := position) positionBound,
          Option.map_some,Option.some.injEq] at range
        exact range.trans (congrArg (fun segment : RangeMapSegment LocationTree => segment.range) selected).symm
      have selectedWithin := preparedData.2.2 cursor segmentBound
      change offset.bytes.toNat ≤ prepared.segments[cursor].range.start.toNat ∧
        prepared.segments[cursor].range.stop.toNat ≤ (offset.bytes+len.bytes).toNat at selectedWithin
      have inside : lower.toNat ≤ current.entries[position].range.start.toNat ∧ current.entries[position].range.stop.toNat ≤ upper.toNat := by
        rw [rangeSame]
        exact ⟨Nat.le_trans requestLower selectedWithin.1,Nat.le_trans selectedWithin.2 requestUpper⟩
      let updated := modify current.entries[position].range current.entries[position].data
      have actual : GeneralBorrowFreshModify.atPosition current position modify = replaced current position currentBound updated := by
        dsimp only [GeneralBorrowFreshModify.atPosition]
        simp only [currentBound,↓reduceDIte]
        rfl
      have next : property (replaced current position currentBound updated) :=
        ⟨(replaced_ranges current position currentBound updated).trans ranges,
          replace_write current position currentBound updated anchor lower upper currentActive inside⟩
      have later := ih (fun other member => included other (by simp [member])) _ next
      simpa only [List.foldl_cons,actual] using later
  rw [GeneralBorrowFreshModify.state_exact map offset len modify well bounds]
  exact (fold prepared.positions.toList (fun _ member => member) prepared.state ⟨rfl,preparedActive⟩).2
end DuplicatePrefix.GeneralBorrowFreshActiveWithinModify
