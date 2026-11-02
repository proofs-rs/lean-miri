import duplicate_prefix.GeneralBorrowFreshActiveWithin
import duplicate_prefix.GeneralBorrowStructuralHistorySifaState
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryActivityGenericRange
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshActiveWithin GeneralBorrowFreshMaterialization GeneralBorrowFreshInstallation GeneralRangeMapOrigins GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem clean (tree : BorrowTree) (index : UniIndex) (ownerKind : AccessKind) (lower upper : UInt64)
    (vacantClean : Every (fun location : LocationTree=>location.perms.get index=none) tree.locations) :
    ActiveWithin tree index ownerKind lower upper := by
  intro point location atPoint state stored accessed kind associated
  obtain ⟨position,valid,_,_,equal⟩ := atPoint
  rw [←equal,vacantClean position valid] at stored
  cases stored

/-- Arbitrary state materialization inside a raw subwindow preserves bytewise
Read/Write activity confinement already formed by earlier, possibly overlapping
segments. No permission transition or operation-success premise is supplied. -/
theorem materialize (tree : BorrowTree) (index : UniIndex) (state : LocationState) (ownerKind : AccessKind) (lower upper : UInt64)
    (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat≤tree.locations.size.bytes.toNat)
    (requestLower : lower.toNat≤offset.bytes.toNat) (requestUpper : (offset.bytes+len.bytes).toNat≤upper.toNat)
    (active : ActiveWithin tree index ownerKind lower upper)
    (stateAllowed : ownerKind=.Read→state.accessed=true→∀kind,state.permission.associatedAccess=some kind→kind=.Read) :
    ActiveWithin {tree with locations:=(tree.locations.modifyRange offset len (fun _ location=>materialized location index state)).state}
      index ownerKind lower upper := by
  let modify := fun (_ : ByteRange) location=>materialized location index state
  let prepared := tree.locations.iterMut offset len
  let updated := (tree.locations.modifyRange offset len modify).state
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have good := preparedData.1
  have preparedActive := GeneralBorrowFreshActiveWithin.refines tree.locations prepared.state preparedData.2.1 index ownerKind lower upper active
  have within := preparedData.2.2
  have sizes : updated.entries.size=prepared.state.entries.size := by
    dsimp only [updated,prepared]
    rw [GeneralBorrowFreshModify.state_exact tree.locations offset len modify well bounds,GeneralBorrowFreshModify.fold_size]
  intro point location valueAt value stored accessed kind associated
  obtain ⟨position,valid,startPoint,pointStop,dataEq⟩ := valueAt
  rw [←dataEq] at stored
  have preparedValid : position<prepared.state.entries.size := by
    have valid' : position<updated.entries.size := valid
    rw[sizes] at valid'
    exact valid'
  obtain ⟨outputValid,entry⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len modify
    (fun _ location=>materialized_idempotent location index state) well bounds position preparedValid
  change updated.entries[position]=(if position∈prepared.positions.toList then
    {prepared.state.entries[position] with data:=modify prepared.state.entries[position].range prepared.state.entries[position].data}
    else prepared.state.entries[position]) at entry
  change updated.entries[position].data.perms.get index=some value at stored
  by_cases selected : position∈prepared.positions.toList
  · simp only [selected,↓reduceIte] at entry
    rw [entry] at stored startPoint pointStop
    have stateEq : value=state := by
      dsimp only [modify,materialized] at stored
      rw [GeneralBorrowFreshLocation.get_same] at stored
      exact Option.some.inj stored.symm
    subst value
    obtain ⟨cursor,cursorValid,same⟩ := Array.mem_iff_getElem.mp (Array.mem_def.mpr selected)
    have selectedGood := good.selected cursor cursorValid
    have segmentValid : cursor<prepared.segments.size := by rw[←good.lengths];exact cursorValid
    have segmentEq : (prepared.segments[cursor]'segmentValid)=prepared.state.entries[position] := by
      have known:=selectedGood.choose_spec
      change prepared.segments[cursor]=prepared.state.entries[prepared.positions[cursor]] at known
      simpa only [same] using known
    have contained:=within cursor segmentValid
    change offset.bytes.toNat≤prepared.segments[cursor].range.start.toNat ∧ prepared.segments[cursor].range.stop.toNat≤(offset.bytes+len.bytes).toNat at contained
    rw[segmentEq] at contained
    dsimp only [modify] at startPoint pointStop
    exact ⟨by omega,by omega,fun mode=>stateAllowed mode accessed kind associated⟩
  · simp only [selected,↓reduceIte] at entry
    rw [entry] at stored startPoint pointStop
    exact preparedActive point prepared.state.entries[position].data ⟨position,preparedValid,startPoint,pointStop,rfl⟩ value stored accessed kind associated
end DuplicatePrefix.GeneralBorrowStructuralHistoryActivityGenericRange
