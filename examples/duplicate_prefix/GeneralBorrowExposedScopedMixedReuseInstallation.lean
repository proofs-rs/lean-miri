import duplicate_prefix.GeneralBorrowExposedScopedMixedShape
import duplicate_prefix.GeneralBorrowExposedScopedSharedReuseChild
import duplicate_prefix.GeneralBorrowFreshSharedInstallation
namespace DuplicatePrefix.GeneralBorrowExposedScopedMixedReuseInstallation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.GeneralBorrowFreshInstallation
open GeneralBorrowExposedScopedMixedShape (Mixed)
open DuplicatePrefix.GeneralBorrowFreshMixedChild
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
/-- Every selected stored location of the real range modifier owns the fresh
Frozen shared child. Preparation, selected values and the full modifier state are
obtained from their actual operations. No outside-allocation ownership premise
or operation-success premise is required. -/
theorem reuse_selected_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (slotBound : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (parentPresent : tree.nodeAt parent = some parentNode)
    (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (support : Nat → Prop) (writable : Nat → Bool)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree default protections).topology)
    (owned : OwnedOn (Mixed tree protections parent support writable)
      offset.bytes (offset.bytes+len.bytes) tree.locations)
    (cursor : Nat) (valid : cursor < (tree.locations.iterMut offset len).positions.size) :
    let indexAt := (tree.locations.iterMut offset len).positions[cursor]
    let changed := tree.locations.modifyRange offset len
      (fun _ location => materialized location index GeneralBorrowFreshAnchor.sharedState)
    ∃ outputValid : indexAt < changed.state.entries.size,
      Mixed
        {(GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)) with
          locations := changed.state}
        protections index (fun position => support position ∨ position = index.toNat) (extend writable index.toNat) (changed.state.entries[indexAt]'outputValid).data := by
  dsimp only
  let prepared := tree.locations.iterMut offset len
  have selected := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    (Mixed tree protections parent support writable) offset.bytes (offset.bytes+len.bytes) owned
    (Nat.le_refl _) (Nat.le_refl _)
  have good := (GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds).1
  obtain ⟨positionValid,same⟩ := good.selected cursor valid
  have segmentValid : cursor < prepared.segments.size := by rw [←good.lengths];exact valid
  have parentOwned := selected.2.2 cursor segmentValid
  rw [same] at parentOwned
  have membership : prepared.positions[cursor] ∈ (tree.locations.iterMut offset len).positions.toList :=
    Array.mem_def.mp (Array.mem_iff_getElem.mpr ⟨cursor,valid,rfl⟩)
  obtain ⟨outputValid,outputEq⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len
    (fun _ location => materialized location index GeneralBorrowFreshAnchor.sharedState)
    (fun _ location => materialized_idempotent location index GeneralBorrowFreshAnchor.sharedState)
    well bounds prepared.positions[cursor] positionValid
  simp only [membership,↓reduceIte] at outputEq
  refine ⟨outputValid,?_⟩
  rw [outputEq]
  have installed := GeneralBorrowExposedScopedSharedReuseChild.reuse_location tree index parent parentNode tag slotBound vacant fits parentPresent
    (prepared.state.entries[prepared.positions[cursor]]'positionValid).data protections writable support forest parentOwned
  rw [GeneralBorrowExposedScopedMixedShape.map_eq]
  simpa only [prepared,GeneralBorrowExposedScopedMixedShape.Mixed] using installed

/-- Slice-local parent ownership is transferred to the fresh child's entire
actual modified slice. The actual iterator covers every overlapping output
segment, so no allocation-wide ownership premise is used. -/
theorem reuse_ranged_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (slotBound : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (parentPresent : tree.nodeAt parent = some parentNode)
    (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (support : Nat → Prop) (writable : Nat → Bool)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree default protections).topology)
    (owned : OwnedOn (Mixed tree protections parent support writable)
      offset.bytes (offset.bytes+len.bytes) tree.locations) :
    let changed := tree.locations.modifyRange offset len
      (fun _ location => materialized location index GeneralBorrowFreshAnchor.sharedState)
    let installed := {(GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshAnchor.sharedNode tag parent)) with
      locations := changed.state}
    OwnedOn (Mixed installed protections index (fun position => support position ∨ position = index.toNat) (extend writable index.toNat))
      offset.bytes (offset.bytes+len.bytes) changed.state := by
  dsimp only
  let prepared := tree.locations.iterMut offset len
  let modify : ByteRange → LocationTree → LocationTree :=
    fun _ location => materialized location index GeneralBorrowFreshAnchor.sharedState
  let changed := tree.locations.modifyRange offset len modify
  have sizes : changed.state.entries.size = prepared.state.entries.size := by
    dsimp only [changed,prepared]
    rw [GeneralBorrowFreshModify.state_exact tree.locations offset len modify well bounds,
      GeneralBorrowFreshModify.fold_size]
  intro position valid positive start stop
  have oldValid : position < prepared.state.entries.size := by rw [←sizes];exact valid
  obtain ⟨outputValid,entryEq⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len modify
    (fun _ location => materialized_idempotent location index GeneralBorrowFreshAnchor.sharedState)
    well bounds position oldValid
  have rangeEq : (changed.state.entries[position]'valid).range = (prepared.state.entries[position]'oldValid).range := by
    have known := congrArg RangeMapSegment.range entryEq
    by_cases member : position ∈ (tree.locations.iterMut offset len).positions.toList
    · simp only [member,↓reduceIte] at known
      exact known
    · simp only [member,↓reduceIte] at known
      exact known
  change (changed.state.entries[position]'valid).range.start.toNat < (offset.bytes+len.bytes).toNat at start
  change offset.bytes.toNat < (changed.state.entries[position]'valid).range.stop.toNat at stop
  rw [rangeEq] at start stop
  obtain ⟨cursor,bounded,same⟩ := GeneralRangeMapCoverage.overlap_selected tree.locations offset len well bounds
    positive position oldValid start stop
  have installed := reuse_selected_owned tree index parent parentNode tag slotBound vacant fits parentPresent offset len well bounds
    protections support writable forest owned cursor bounded
  dsimp only at installed
  rw [same] at installed
  exact installed.choose_spec



end DuplicatePrefix.GeneralBorrowExposedScopedMixedReuseInstallation
