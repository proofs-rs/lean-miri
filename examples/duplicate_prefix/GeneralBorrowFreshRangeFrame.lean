import duplicate_prefix.GeneralBorrowFreshModify
import duplicate_prefix.GeneralRangeMapOriginPrepare

namespace DuplicatePrefix.GeneralBorrowFreshRangeFrame
open Miri.ABI Miri.DataStructures
open DuplicatePrefix.GeneralRangeMapState GeneralBorrowFreshModify

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- One actual modifier update keeps the segment geometry and therefore the
well-formedness and total size of a range map. The callback is unrestricted. -/
theorem atPosition_wellFormed (map : DedupRangeMap α) (position : Nat)
    (modify : ByteRange → α → α) (well : map.WellFormed) :
    (GeneralBorrowFreshModify.atPosition map position modify).WellFormed := by
  unfold GeneralBorrowFreshModify.atPosition
  split
  · rename_i valid
    let data := modify map.entries[position].range map.entries[position].data
    change (replaced map position valid data).WellFormed
    exact replaced_wellFormed map position valid data well
  · exact well

theorem atPosition_size (map : DedupRangeMap α) (position : Nat)
    (modify : ByteRange → α → α) :
    (GeneralBorrowFreshModify.atPosition map position modify).size = map.size := by
  unfold GeneralBorrowFreshModify.atPosition
  split
  · rename_i valid
    let data := modify map.entries[position].range map.entries[position].data
    change (replaced map position valid data).size = map.size
    exact replaced_size map position valid data
  · rfl

private theorem fold_wellFormed (positions : List Nat) (modify : ByteRange → α → α)
    (map : DedupRangeMap α) (well : map.WellFormed) :
    (positions.foldl (fun current position =>
      GeneralBorrowFreshModify.atPosition current position modify) map).WellFormed := by
  induction positions generalizing map with
  | nil => exact well
  | cons position rest ih =>
      exact ih _ (atPosition_wellFormed map position modify well)

private theorem fold_size (positions : List Nat) (modify : ByteRange → α → α)
    (map : DedupRangeMap α) :
    (positions.foldl (fun current position =>
      GeneralBorrowFreshModify.atPosition current position modify) map).size = map.size := by
  induction positions generalizing map with
  | nil => rfl
  | cons position rest ih =>
      rw [List.foldl_cons, ih, atPosition_size]

/-- The genuine DedupRangeMap.modifyRange result preserves well-formedness and
total size for every pure callback, given only a well-formed input partition
and the request's in-bounds condition. Preparation success is derived through
the actual iterator's origin/geometry proof. -/
theorem modifyRange_frame {α : Type} [DecidableEq α] (map : DedupRangeMap α)
    (offset len : Size) (modify : ByteRange → α → α)
    (well : map.WellFormed)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ map.size.bytes.toNat) :
    (map.modifyRange offset len modify).state.WellFormed ∧
      (map.modifyRange offset len modify).state.size.bytes = map.size.bytes := by
  let prepared := map.iterMut offset len
  have preparedGood := GeneralRangeMapOriginPrepare.iter_mut map offset len well bounds
  have preparedWell : prepared.state.WellFormed := preparedGood.1.wellFormed
  have preparedSize : prepared.state.size.bytes = map.size.bytes := preparedGood.1.capacity
  have exactState := GeneralBorrowFreshModify.state_exact map offset len modify well bounds
  constructor
  · rw [exactState]
    exact fold_wellFormed prepared.positions.toList modify prepared.state preparedWell
  · rw [exactState]
    rw [fold_size]
    exact preparedSize

end DuplicatePrefix.GeneralBorrowFreshRangeFrame

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.GeneralBorrowFreshRangeFrame.modifyRange_frame) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual range-map frame dependency {dependency}"
