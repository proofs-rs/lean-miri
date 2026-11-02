import duplicate_prefix.GeneralRangeMapOrigins
import duplicate_prefix.GeneralRangeMapFind

/-! Physical-byte observations use the actual source binary search and
segment indexer. They remain independent of segment splitting and reindexing. -/
namespace DuplicatePrefix.GeneralRangeMapByteLookup
open Miri Miri.ABI Miri.DataStructures
open GeneralRangeMapState GeneralRangeMapOrigins GeneralRangeMapGeometry RangeMapNonempty
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def lookup {α : Type} (map : DedupRangeMap α) (point : UInt64) : Except DedupRangeMapError α := do
  let position ← range_find_offset map point
  let segment ← map.index position
  return segment.data

theorem value_unique {α : Type} (map : DedupRangeMap α) (well : map.WellFormed)
    (point : UInt64) (first second : α)
    (left : ValueAt map point first) (right : ValueAt map point second) : first = second := by
  obtain ⟨i,iv,il,iu,ie⟩ := left
  obtain ⟨j,jv,jl,ju,je⟩ := right
  have same : i = j := by
    by_cases before : i < j
    · have separation := stop_le_start map well i j before jv
      omega
    · by_cases after : j < i
      · have separation := stop_le_start map well j i after iv
        omega
      · omega
  subst j
  exact ie.symm.trans je

theorem lookup_success {α : Type} (map : DedupRangeMap α) (well : map.WellFormed)
    (point : UInt64) (inside : point.toNat < map.size.bytes.toNat) :
    ∃ value, ValueAt map point value ∧ lookup map point = .ok value := by
  obtain ⟨position,found,valid,start,stop⟩ := GeneralRangeMapFind.find_success map point well inside
  refine ⟨map.entries[position].data,⟨position,valid,start,stop,rfl⟩,?_⟩
  simp only [lookup,found,index_exact map position valid,Except.bind,bind,pure,Except.pure]

private theorem value_inside {α : Type} (map : DedupRangeMap α) (well : map.WellFormed)
    (point : UInt64) (value : α) (observed : ValueAt map point value) :
    point.toNat < map.size.bytes.toNat := by
  obtain ⟨position,valid,start,stop,_⟩ := observed
  have nonempty : 0 < map.entries.size := by omega
  rw [size_last map nonempty]
  by_cases last : position = map.entries.size-1
  · simpa only [←last] using stop
  · have earlier : position < map.entries.size-1 := by omega
    have separation := stop_le_start map well position (map.entries.size-1) earlier (by omega)
    have positive := (facts map well (by omega)).2.1 (map.entries.size-1) (by omega)
    omega

theorem lookup_of_value {α : Type} (map : DedupRangeMap α) (well : map.WellFormed)
    (point : UInt64) (value : α) (observed : ValueAt map point value) :
    lookup map point = .ok value := by
  obtain ⟨found,actual,success⟩ := lookup_success map well point (value_inside map well point value observed)
  have same := value_unique map well point found value actual observed
  simpa only [same] using success

/-- Pointwise refinement at this byte identifies its actual lookup, even
when preparation has split segments or changed their vector positions. -/
theorem equal_of_refines {α : Type} (original current : DedupRangeMap α)
    (originalWell : original.WellFormed) (currentWell : current.WellFormed)
    (capacity : current.size = original.size) (point : UInt64)
    (refines : ∀ value, ValueAt current point value → ValueAt original point value)
    (inside : point.toNat < original.size.bytes.toNat) :
    lookup current point = lookup original point := by
  have currentInside : point.toNat < current.size.bytes.toNat := by rw [capacity];exact inside
  obtain ⟨value,observed,success⟩ := lookup_success current currentWell point currentInside
  exact success.trans (lookup_of_value original originalWell point value (refines value observed)).symm

end DuplicatePrefix.GeneralRangeMapByteLookup

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralRangeMapByteLookup." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved physical-byte lookup dependency {dependency}"
