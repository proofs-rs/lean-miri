import duplicate_prefix.GeneralBorrowFreshReleaseLoop
import duplicate_prefix.GeneralBorrowFreshOwnedOn
namespace DuplicatePrefix.GeneralBorrowFreshActiveOn
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralBorrowFreshInstallation
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowView
open DuplicatePrefix.GeneralBorrowFreshAnchor DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A fresh/reused permission slot is materialized only in the selected slice.
The old-slot cleanliness premise is data (provided by GC for reuse), not a
successful-operation assumption. Actual preparation and modifier are used. -/
theorem modified (tree : BorrowTree) (index : UniIndex) (offset len : Size)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none) :
    let updated := (tree.locations.modifyRange offset len (fun _ location => materialized location index sharedState)).state
    GeneralBorrowFreshReleaseLoop.ActiveOn {tree with locations := updated} index .Read offset.bytes (offset.bytes+len.bytes) := by
  dsimp only
  let modify := fun (_ : ByteRange) location => materialized location index sharedState
  let prepared := tree.locations.iterMut offset len
  let updated := (tree.locations.modifyRange offset len modify).state
  have good := GeneralRangeMapSafety.iter_mut (fun location : LocationTree => location.perms.get index = none)
    tree.locations offset len well clean bounds
  have within := (GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds).2.2
  have sizes : updated.entries.size = prepared.state.entries.size := by
    dsimp only [updated,prepared]
    rw [GeneralBorrowFreshModify.state_exact tree.locations offset len modify well bounds,
      GeneralBorrowFreshModify.fold_size]
  intro position valid state stored active kind associated
  have preparedValid : position < prepared.state.entries.size := by
    have valid' : position < updated.entries.size := valid
    rw [sizes] at valid'
    exact valid'
  obtain ⟨outputValid,entry⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len modify
    (fun _ location => materialized_idempotent location index sharedState) well bounds position preparedValid
  change updated.entries[position] =
    (if position ∈ prepared.positions.toList then
      {prepared.state.entries[position] with data := modify prepared.state.entries[position].range prepared.state.entries[position].data}
    else prepared.state.entries[position]) at entry
  change updated.entries[position].data.perms.get index = some state at stored
  change updated.entries[position].range.start.toNat < (offset.bytes+len.bytes).toNat ∧
    offset.bytes.toNat < updated.entries[position].range.stop.toNat ∧ (AccessKind.Read = AccessKind.Read → kind = .Read)
  by_cases selected : position ∈ prepared.positions.toList
  · simp only [selected,↓reduceIte] at entry
    rw [entry] at stored ⊢
    have stateEq : state = sharedState := by
      dsimp only [modify,materialized] at stored
      rw [GeneralBorrowFreshLocation.get_same] at stored
      exact Option.some.inj stored.symm
    subst state
    have kindEq : kind = .Read := by simpa only [sharedState,Permission.associatedAccess,Option.some.injEq] using associated.symm
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
    have positive := (GeneralRangeMapGeometry.facts prepared.state good.wellFormed (by omega)).2.1 position preparedValid
    dsimp only [modify]
    exact ⟨by omega,by omega,fun _ => kindEq⟩
  · simp only [selected,↓reduceIte] at entry
    rw [entry,good.every position preparedValid] at stored
    cases stored

private theorem lookup_shape (location : LocationTree) (anchor : UniIndex) :
    (⟨locationShape location⟩ : UniValMap StateShape).get anchor = (location.perms.get anchor).map stateShape := by
  unfold locationShape UniValMap.get
  simp only [Array.getElem?_map]
  cases slot : location.perms.data[anchor.toNat]? with
  | none => rfl
  | some entry => cases entry <;> rfl

/-- Preserving permission/accessed shapes preserves the active-range profile;
SIFA changes and node metadata do not affect which locations are active. -/
theorem shape_preserves (before after : BorrowTree) (same : treeShape after = treeShape before)
    (anchor : UniIndex) (kind : AccessKind) (lower upper : UInt64)
    (active : GeneralBorrowFreshReleaseLoop.ActiveOn before anchor kind lower upper) :
    GeneralBorrowFreshReleaseLoop.ActiveOn after anchor kind lower upper := by
  have ranges : after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
      before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) :=
    congrArg (fun row => row.2.2.1) same
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    have known := congrArg Array.size ranges
    simpa only [Array.size_map] using known
  intro position valid state stored accessed accessKind associated
  have beforeValid : position < before.locations.entries.size := by rw [←sizes];exact valid
  have entriesSame : after.locations.entries[position].range = before.locations.entries[position].range ∧
      locationShape after.locations.entries[position].data = locationShape before.locations.entries[position].data := by
    have known := congrArg (fun rows => rows[position]?) ranges
    simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,
      Array.getElem?_eq_getElem beforeValid,Option.map_some] at known
    exact Prod.mk.inj (Option.some.inj known)
  have profiles := congrArg (fun data => (⟨data⟩ : UniValMap StateShape).get anchor) entriesSame.2
  rw [lookup_shape,lookup_shape,stored] at profiles
  cases old : before.locations.entries[position].data.perms.get anchor with
  | none => simp only [old,Option.map_none,Option.map_some] at profiles;cases profiles
  | some oldState =>
    have pair : stateShape state = stateShape oldState := by
      simpa only [old,Option.map_some,Option.some.injEq] using profiles
    have permission : state.permission = oldState.permission := congrArg Prod.fst pair
    have access : state.accessed = oldState.accessed := congrArg Prod.snd pair
    have oldActive : oldState.accessed = true := access.symm.trans accessed
    have oldAssociated : oldState.permission.associatedAccess = some accessKind := by rw [←permission];exact associated
    have result := active position beforeValid oldState old oldActive accessKind oldAssociated
    rw [entriesSame.1]
    exact result

/-- The actual SIFA propagation retains the active-range profile, independently
of completion; constructor theorems derive that completion separately. -/
theorem sifa_preserves (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (anchor : UniIndex) (kind : AccessKind) (lower upper : UInt64)
    (active : GeneralBorrowFreshReleaseLoop.ActiveOn tree anchor kind lower upper) :
    GeneralBorrowFreshReleaseLoop.ActiveOn (sourceUpdateSifa tree start strongest).1 anchor kind lower upper := by
  exact shape_preserves tree _ (GeneralBorrowSifaView.preserves tree start strongest) anchor kind lower upper active
end DuplicatePrefix.GeneralBorrowFreshActiveOn
