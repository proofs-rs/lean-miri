import duplicate_prefix.GeneralBorrowFreshActiveWithin
namespace DuplicatePrefix.GeneralBorrowFreshActiveWithinInsert
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralBorrowFreshInstallation
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshActiveWithin
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Any fixed new permission state gets a pointwise active-range profile from
slot cleanliness and the real range modifier. The state typing condition is
vacuous for mutable owners and explicit for shared owners. -/
theorem modified (tree : BorrowTree) (index : UniIndex) (offset len : Size) (inserted : LocationState) (ownerKind : AccessKind)
    (allowed : ∀ kind, inserted.permission.associatedAccess = some kind → ownerKind = .Read → kind = .Read)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none) :
    let updated := (tree.locations.modifyRange offset len (fun _ location => materialized location index inserted)).state
    ActiveWithin {tree with locations := updated} index ownerKind offset.bytes (offset.bytes+len.bytes) := by
  dsimp only
  let modify := fun (_ : ByteRange) location => materialized location index inserted
  let prepared := tree.locations.iterMut offset len
  let updated := (tree.locations.modifyRange offset len modify).state
  have good := GeneralRangeMapSafety.iter_mut (fun location : LocationTree => location.perms.get index = none)
    tree.locations offset len well clean bounds
  have within := (GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds).2.2
  have sizes : updated.entries.size = prepared.state.entries.size := by
    dsimp only [updated,prepared]
    rw [GeneralBorrowFreshModify.state_exact tree.locations offset len modify well bounds,
      GeneralBorrowFreshModify.fold_size]
  intro point location valueAt state stored active kind associated
  obtain ⟨position,valid,startPoint,pointStop,dataEq⟩ := valueAt
  rw [←dataEq] at stored
  have preparedValid : position < prepared.state.entries.size := by
    have valid' : position < updated.entries.size := valid
    rw [sizes] at valid'
    exact valid'
  obtain ⟨outputValid,entry⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len modify
    (fun _ location => materialized_idempotent location index inserted) well bounds position preparedValid
  change updated.entries[position] =
    (if position ∈ prepared.positions.toList then
      {prepared.state.entries[position] with data := modify prepared.state.entries[position].range prepared.state.entries[position].data}
    else prepared.state.entries[position]) at entry
  change updated.entries[position].data.perms.get index = some state at stored
  change offset.bytes.toNat ≤ point.toNat ∧ point.toNat < (offset.bytes+len.bytes).toNat ∧
    (ownerKind = .Read → kind = .Read)
  by_cases selected : position ∈ prepared.positions.toList
  · simp only [selected,↓reduceIte] at entry
    rw [entry] at stored startPoint pointStop
    have stateEq : state = inserted := by
      dsimp only [modify,materialized] at stored
      rw [GeneralBorrowFreshLocation.get_same] at stored
      exact Option.some.inj stored.symm
    subst state
    have kindOK : ownerKind = .Read → kind = .Read := allowed kind associated
    obtain ⟨cursor,cursorValid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_def.mpr selected)
    have selectedGood := good.selected cursor cursorValid
    have segmentValid : cursor < prepared.segments.size := by rw [←good.lengths];exact cursorValid
    have segmentEq : (prepared.segments[cursor]'segmentValid) = prepared.state.entries[position] := by
      have known := selectedGood.choose_spec
      change prepared.segments[cursor] = prepared.state.entries[prepared.positions[cursor]] at known
      simpa only [same] using known
    have contained := within cursor segmentValid
    change offset.bytes.toNat ≤ prepared.segments[cursor].range.start.toNat ∧
      prepared.segments[cursor].range.stop.toNat ≤ (offset.bytes+len.bytes).toNat at contained
    rw [segmentEq] at contained
    dsimp only [modify] at startPoint pointStop
    exact ⟨by omega,by omega,kindOK⟩
  · simp only [selected,↓reduceIte] at entry
    rw [entry,good.every position preparedValid] at stored
    cases stored
end DuplicatePrefix.GeneralBorrowFreshActiveWithinInsert
