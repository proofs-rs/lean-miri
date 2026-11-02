import duplicate_prefix.GeneralBorrowFreshDefaultChild
import duplicate_prefix.GeneralBorrowFreshReuseAnchor
import duplicate_prefix.GeneralBorrowFreshInstallation
namespace DuplicatePrefix.GeneralBorrowFreshDefaultInstallation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.GeneralBorrowFreshInstallation DuplicatePrefix.GeneralBorrowFreshDefaultChild
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem append_location_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags)
    (owned : GeneralBorrowRange.LocationOwned tree protections parent .Write location) :
    GeneralBorrowRange.LocationOwned (GeneralBorrowFreshGraph.attached tree index parent parentNode (child tag parent))
      protections index .Write (materialized location index inside) := by
  obtain ⟨⟨forest⟩,owner⟩ := owned
  refine ⟨⟨GeneralBorrowFreshProjection.projected_forest tree index parent parentNode (child tag parent)
    atEnd parentPresent rfl rfl location (materialized location index inside) protections forest⟩,?_⟩
  exact GeneralBorrowFreshAnchor.anchor_owned tree index parent parentNode (child tag parent) atEnd parentPresent rfl rfl
    location inside protections .Write forest owner (fun held => GeneralBorrowPermissions.fresh_mutable_owned .Read true held)

theorem reuse_location_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (parentPresent : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags)
    (owned : GeneralBorrowRange.LocationOwned tree protections parent .Write location) :
    GeneralBorrowRange.LocationOwned (GeneralBorrowFreshGraph.attached tree index parent parentNode (child tag parent))
      protections index .Write (materialized location index inside) := by
  obtain ⟨⟨forest⟩,owner⟩ := owned
  refine ⟨⟨GeneralBorrowFreshReuseProjection.projected_forest tree index parent parentNode (child tag parent)
    bounded vacant parentPresent rfl rfl location (materialized location index inside) protections forest⟩,?_⟩
  exact GeneralBorrowFreshReuseAnchor.anchor_owned tree index parent parentNode (child tag parent) bounded vacant fits
    parentPresent rfl rfl location inside protections .Write forest owner
      (fun held => GeneralBorrowPermissions.fresh_mutable_owned .Read true held)

/-- Every selected stored location of the real range modifier owns the fresh
unprotected mutable-expression child. Preparation, selected values and the full modifier state are
obtained from their actual operations. No outside-allocation ownership premise
or operation-success premise is required. -/
theorem append_selected_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write)
      offset.bytes (offset.bytes+len.bytes) tree.locations)
    (cursor : Nat) (valid : cursor < (tree.locations.iterMut offset len).positions.size) :
    let indexAt := (tree.locations.iterMut offset len).positions[cursor]
    let changed := tree.locations.modifyRange offset len
      (fun _ location => materialized location index GeneralBorrowFreshDefaultChild.inside)
    ∃ outputValid : indexAt < changed.state.entries.size,
      GeneralBorrowRange.LocationOwned
        {(GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshDefaultChild.child tag parent)) with
          locations := changed.state}
        protections index .Write (changed.state.entries[indexAt]'outputValid).data := by
  dsimp only
  let prepared := tree.locations.iterMut offset len
  have selected := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    (GeneralBorrowRange.LocationOwned tree protections parent .Write) offset.bytes (offset.bytes+len.bytes) owned
    (Nat.le_refl _) (Nat.le_refl _)
  have good := (GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds).1
  obtain ⟨positionValid,same⟩ := good.selected cursor valid
  have segmentValid : cursor < prepared.segments.size := by rw [←good.lengths];exact valid
  have parentOwned := selected.2.2 cursor segmentValid
  rw [same] at parentOwned
  have membership : prepared.positions[cursor] ∈ (tree.locations.iterMut offset len).positions.toList :=
    Array.mem_def.mp (Array.mem_iff_getElem.mpr ⟨cursor,valid,rfl⟩)
  obtain ⟨outputValid,outputEq⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len
    (fun _ location => materialized location index GeneralBorrowFreshDefaultChild.inside)
    (fun _ location => materialized_idempotent location index GeneralBorrowFreshDefaultChild.inside)
    well bounds prepared.positions[cursor] positionValid
  simp only [membership,↓reduceIte] at outputEq
  refine ⟨outputValid,?_⟩
  rw [outputEq]
  have installed := append_location_owned tree index parent parentNode tag atEnd parentPresent
    (prepared.state.entries[prepared.positions[cursor]]'positionValid).data protections parentOwned
  rw [location_map]
  simpa only [prepared] using installed

/-- Slice-local parent ownership is transferred to the fresh child's entire
actual modified slice. The actual iterator covers every overlapping output
segment, so no allocation-wide ownership premise is used. -/
theorem append_ranged_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write)
      offset.bytes (offset.bytes+len.bytes) tree.locations) :
    let changed := tree.locations.modifyRange offset len
      (fun _ location => materialized location index GeneralBorrowFreshDefaultChild.inside)
    let installed := {(GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshDefaultChild.child tag parent)) with
      locations := changed.state}
    OwnedOn (GeneralBorrowRange.LocationOwned installed protections index .Write)
      offset.bytes (offset.bytes+len.bytes) changed.state := by
  dsimp only
  let prepared := tree.locations.iterMut offset len
  let modify : ByteRange → LocationTree → LocationTree :=
    fun _ location => materialized location index GeneralBorrowFreshDefaultChild.inside
  let changed := tree.locations.modifyRange offset len modify
  have sizes : changed.state.entries.size = prepared.state.entries.size := by
    dsimp only [changed,prepared]
    rw [GeneralBorrowFreshModify.state_exact tree.locations offset len modify well bounds,
      GeneralBorrowFreshModify.fold_size]
  intro position valid positive start stop
  have oldValid : position < prepared.state.entries.size := by rw [←sizes];exact valid
  obtain ⟨outputValid,entryEq⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len modify
    (fun _ location => materialized_idempotent location index GeneralBorrowFreshDefaultChild.inside)
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
  have installed := append_selected_owned tree index parent parentNode tag atEnd parentPresent offset len well bounds
    protections owned cursor bounded
  dsimp only at installed
  rw [same] at installed
  exact installed.choose_spec


/-- Every selected stored location of the real range modifier owns the fresh
unprotected mutable-expression child. Preparation, selected values and the full modifier state are
obtained from their actual operations. No outside-allocation ownership premise
or operation-success premise is required. -/
theorem reuse_selected_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (indexBound : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (parentPresent : tree.nodeAt parent = some parentNode)
    (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write)
      offset.bytes (offset.bytes+len.bytes) tree.locations)
    (cursor : Nat) (valid : cursor < (tree.locations.iterMut offset len).positions.size) :
    let indexAt := (tree.locations.iterMut offset len).positions[cursor]
    let changed := tree.locations.modifyRange offset len
      (fun _ location => materialized location index GeneralBorrowFreshDefaultChild.inside)
    ∃ outputValid : indexAt < changed.state.entries.size,
      GeneralBorrowRange.LocationOwned
        {(GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshDefaultChild.child tag parent)) with
          locations := changed.state}
        protections index .Write (changed.state.entries[indexAt]'outputValid).data := by
  dsimp only
  let prepared := tree.locations.iterMut offset len
  have selected := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    (GeneralBorrowRange.LocationOwned tree protections parent .Write) offset.bytes (offset.bytes+len.bytes) owned
    (Nat.le_refl _) (Nat.le_refl _)
  have good := (GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds).1
  obtain ⟨positionValid,same⟩ := good.selected cursor valid
  have segmentValid : cursor < prepared.segments.size := by rw [←good.lengths];exact valid
  have parentOwned := selected.2.2 cursor segmentValid
  rw [same] at parentOwned
  have membership : prepared.positions[cursor] ∈ (tree.locations.iterMut offset len).positions.toList :=
    Array.mem_def.mp (Array.mem_iff_getElem.mpr ⟨cursor,valid,rfl⟩)
  obtain ⟨outputValid,outputEq⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len
    (fun _ location => materialized location index GeneralBorrowFreshDefaultChild.inside)
    (fun _ location => materialized_idempotent location index GeneralBorrowFreshDefaultChild.inside)
    well bounds prepared.positions[cursor] positionValid
  simp only [membership,↓reduceIte] at outputEq
  refine ⟨outputValid,?_⟩
  rw [outputEq]
  have installed := reuse_location_owned tree index parent parentNode tag indexBound vacant fits parentPresent
    (prepared.state.entries[prepared.positions[cursor]]'positionValid).data protections parentOwned
  rw [location_map]
  simpa only [prepared] using installed

/-- Slice-local parent ownership is transferred to the fresh child's entire
actual modified slice. The actual iterator covers every overlapping output
segment, so no allocation-wide ownership premise is used. -/
theorem reuse_ranged_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (indexBound : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (parentPresent : tree.nodeAt parent = some parentNode)
    (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write)
      offset.bytes (offset.bytes+len.bytes) tree.locations) :
    let changed := tree.locations.modifyRange offset len
      (fun _ location => materialized location index GeneralBorrowFreshDefaultChild.inside)
    let installed := {(GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshDefaultChild.child tag parent)) with
      locations := changed.state}
    OwnedOn (GeneralBorrowRange.LocationOwned installed protections index .Write)
      offset.bytes (offset.bytes+len.bytes) changed.state := by
  dsimp only
  let prepared := tree.locations.iterMut offset len
  let modify : ByteRange → LocationTree → LocationTree :=
    fun _ location => materialized location index GeneralBorrowFreshDefaultChild.inside
  let changed := tree.locations.modifyRange offset len modify
  have sizes : changed.state.entries.size = prepared.state.entries.size := by
    dsimp only [changed,prepared]
    rw [GeneralBorrowFreshModify.state_exact tree.locations offset len modify well bounds,
      GeneralBorrowFreshModify.fold_size]
  intro position valid positive start stop
  have oldValid : position < prepared.state.entries.size := by rw [←sizes];exact valid
  obtain ⟨outputValid,entryEq⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len modify
    (fun _ location => materialized_idempotent location index GeneralBorrowFreshDefaultChild.inside)
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
  have installed := reuse_selected_owned tree index parent parentNode tag indexBound vacant fits parentPresent offset len well bounds
    protections owned cursor bounded
  dsimp only at installed
  rw [same] at installed
  exact installed.choose_spec

end DuplicatePrefix.GeneralBorrowFreshDefaultInstallation
#print axioms DuplicatePrefix.GeneralBorrowFreshDefaultInstallation.append_ranged_owned
#print axioms DuplicatePrefix.GeneralBorrowFreshDefaultInstallation.reuse_ranged_owned
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshDefaultInstallation." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved frozen slice installation dependency {dependency}"
