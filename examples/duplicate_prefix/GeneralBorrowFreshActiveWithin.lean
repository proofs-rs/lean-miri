import duplicate_prefix.GeneralBorrowFreshActiveOn
namespace DuplicatePrefix.GeneralBorrowFreshActiveWithin
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralBorrowFreshInstallation
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowView
open DuplicatePrefix.GeneralBorrowFreshAnchor DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Every byte represented by an active stored state belongs to its owned
interval. This pointwise outside-inactivity contract survives splitting and
raw-data-equal merges, unlike a mere segment-overlap condition. -/
def Profile (map : DedupRangeMap LocationTree) (index : UniIndex) (ownerKind : AccessKind)
    (lower upper : UInt64) : Prop :=
  ∀ point location, ValueAt map point location → ∀ state,
    location.perms.get index = some state → state.accessed = true →
    ∀ kind, state.permission.associatedAccess = some kind →
      lower.toNat ≤ point.toNat ∧ point.toNat < upper.toNat ∧ (ownerKind = .Read → kind = .Read)

def ActiveWithin (tree : BorrowTree) (index : UniIndex) (ownerKind : AccessKind) (lower upper : UInt64) : Prop :=
  Profile tree.locations index ownerKind lower upper

theorem refines (before after : DedupRangeMap LocationTree) (refined : Refines before after)
    (index : UniIndex) (ownerKind : AccessKind) (lower upper : UInt64)
    (active : Profile before index ownerKind lower upper) : Profile after index ownerKind lower upper := by
  intro point location atPoint
  exact active point location (refined point location atPoint)

/-- The stronger bytewise profile supplies the release loop's active overlap
condition on any well-formed positive segments. -/
theorem active_on (tree : BorrowTree) (index : UniIndex) (ownerKind : AccessKind) (lower upper : UInt64)
    (well : tree.locations.WellFormed) (active : ActiveWithin tree index ownerKind lower upper) :
    GeneralBorrowFreshReleaseLoop.ActiveOn tree index ownerKind lower upper := by
  intro position valid state stored accessed kind associated
  have positive := (GeneralRangeMapGeometry.facts tree.locations well (by omega)).2.1 position valid
  have profile := active tree.locations.entries[position].range.start tree.locations.entries[position].data
    ⟨position,valid,Nat.le_refl _,positive,rfl⟩ state stored accessed kind associated
  exact ⟨profile.2.1,by omega,profile.2.2⟩

/-- Clean new slots become active only at requested bytes under the actual
Frozen-state modifier. No success or inactive-outside outcome is assumed. -/
theorem modified (tree : BorrowTree) (index : UniIndex) (offset len : Size)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get index = none) :
    let updated := (tree.locations.modifyRange offset len (fun _ location => materialized location index sharedState)).state
    ActiveWithin {tree with locations := updated} index .Read offset.bytes (offset.bytes+len.bytes) := by
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
  intro point location valueAt state stored active kind associated
  obtain ⟨position,valid,startPoint,pointStop,dataEq⟩ := valueAt
  rw [←dataEq] at stored
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
  change offset.bytes.toNat ≤ point.toNat ∧ point.toNat < (offset.bytes+len.bytes).toNat ∧
    (AccessKind.Read = AccessKind.Read → kind = .Read)
  by_cases selected : position ∈ prepared.positions.toList
  · simp only [selected,↓reduceIte] at entry
    rw [entry] at stored startPoint pointStop
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
    dsimp only [modify] at startPoint pointStop
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
    (active : ActiveWithin before anchor kind lower upper) :
    ActiveWithin after anchor kind lower upper := by
  have ranges : after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
      before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) :=
    congrArg (fun row => row.2.2.1) same
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    have known := congrArg Array.size ranges
    simpa only [Array.size_map] using known
  intro point location valueAt state stored accessed accessKind associated
  obtain ⟨position,valid,startPoint,pointStop,dataEq⟩ := valueAt
  rw [←dataEq] at stored
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
    have oldValue : ValueAt before.locations point before.locations.entries[position].data := by
      refine ⟨position,beforeValid,?_,?_,rfl⟩
      · rw [←entriesSame.1];exact startPoint
      · rw [←entriesSame.1];exact pointStop
    exact active point before.locations.entries[position].data oldValue oldState old oldActive accessKind oldAssociated

theorem sifa_preserves (tree : BorrowTree) (start : UniIndex) (strongest : IdempotentForeignAccess)
    (anchor : UniIndex) (kind : AccessKind) (lower upper : UInt64)
    (active : ActiveWithin tree anchor kind lower upper) :
    ActiveWithin (sourceUpdateSifa tree start strongest).1 anchor kind lower upper := by
  exact shape_preserves tree _ (GeneralBorrowSifaView.preserves tree start strongest) anchor kind lower upper active

theorem to_write (tree : BorrowTree) (anchor : UniIndex) (lower upper : UInt64)
    (active : ActiveWithin tree anchor .Read lower upper) : ActiveWithin tree anchor .Write lower upper := by
  intro point location atPoint state stored accessed kind associated
  have known := active point location atPoint state stored accessed kind associated
  exact ⟨known.1,known.2.1,by intro impossible;cases impossible⟩
end DuplicatePrefix.GeneralBorrowFreshActiveWithin
