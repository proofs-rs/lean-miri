import duplicate_prefix.GeneralBorrowFreshModify
import duplicate_prefix.GeneralBorrowFreshAnchor
import duplicate_prefix.GeneralRangeMapCoverage
namespace DuplicatePrefix.GeneralBorrowFreshInstallation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

theorem insert_idempotent {α : Type} (map : UniValMap α) (index : UniIndex) (value : α) :
    (map.insert index value).insert index value = map.insert index value := by
  have present := GeneralBorrowFreshLocation.get_same map index value
  have valid := lookup_valid (map.insert index value) index value present
  have cell : (map.insert index value).data[index.toNat]'valid = some value := by
    simpa only [UniValMap.get,Array.getElem?_eq_getElem valid] using present
  have dataEq := insert_existing (map.insert index value) index value value present
  rw [←cell,Array.set_getElem_self] at dataEq
  have injective : ∀ left right : UniValMap α, left.data = right.data → left = right := by
    intro left right
    cases left;cases right
    intro same;cases same;rfl
  exact injective _ _ dataEq

theorem materialized_idempotent (location : LocationTree) (index : UniIndex) (state : LocationState) :
    materialized (materialized location index state) index state = materialized location index state := by
  simp only [materialized,insert_idempotent]

/-- Tag-map and range-map context do not alter a projection at a supplied
location. This transfers per-location ownership to the constructor's actual
bookkeeping records without premises on unrelated locations. -/
theorem location_context (tree : BorrowTree) (mapping : UniKeyMap BorTag)
    (locations : DedupRangeMap LocationTree) (location : LocationTree)
    (protections : ProtectedTags) (anchor : UniIndex) (kind : AccessKind)
    (owned : GeneralBorrowRange.LocationOwned tree protections anchor kind location) :
    GeneralBorrowRange.LocationOwned {tree with tagMapping := mapping,locations := locations}
      protections anchor kind location := by
  exact owned

theorem location_map (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (location : LocationTree) (protections : ProtectedTags) (anchor : UniIndex) (kind : AccessKind) :
    GeneralBorrowRange.LocationOwned {tree with locations := locations} protections anchor kind location =
      GeneralBorrowRange.LocationOwned tree protections anchor kind location := rfl

theorem location_context_eq (tree : BorrowTree) (mapping : UniKeyMap BorTag)
    (locations : DedupRangeMap LocationTree) (location : LocationTree)
    (protections : ProtectedTags) (anchor : UniIndex) (kind : AccessKind) :
    GeneralBorrowRange.LocationOwned {tree with tagMapping := mapping,locations := locations}
      protections anchor kind location = GeneralBorrowRange.LocationOwned tree protections anchor kind location := rfl

/-- Every selected stored location of the real range modifier owns the fresh
mutable child. Preparation, selected values and the full modifier state are
obtained from their actual operations. No outside-allocation ownership premise
or operation-success premise is required. -/
theorem selected_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (kind : AccessKind)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent kind)
      offset.bytes (offset.bytes+len.bytes) tree.locations)
    (cursor : Nat) (valid : cursor < (tree.locations.iterMut offset len).positions.size) :
    let indexAt := (tree.locations.iterMut offset len).positions[cursor]
    let changed := tree.locations.modifyRange offset len
      (fun _ location => materialized location index GeneralBorrowFreshChild.inside)
    ∃ outputValid : indexAt < changed.state.entries.size,
      GeneralBorrowRange.LocationOwned
        {(GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshChild.child tag parent)) with
          locations := changed.state}
        protections index kind (changed.state.entries[indexAt]'outputValid).data := by
  dsimp only
  let prepared := tree.locations.iterMut offset len
  have selected := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    (GeneralBorrowRange.LocationOwned tree protections parent kind) offset.bytes (offset.bytes+len.bytes) owned
    (Nat.le_refl _) (Nat.le_refl _)
  have good := (GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds).1
  obtain ⟨positionValid,same⟩ := good.selected cursor valid
  have segmentValid : cursor < prepared.segments.size := by rw [←good.lengths];exact valid
  have parentOwned := selected.2.2 cursor segmentValid
  rw [same] at parentOwned
  have membership : prepared.positions[cursor] ∈ (tree.locations.iterMut offset len).positions.toList :=
    Array.mem_def.mp (Array.mem_iff_getElem.mpr ⟨cursor,valid,rfl⟩)
  obtain ⟨outputValid,outputEq⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len
    (fun _ location => materialized location index GeneralBorrowFreshChild.inside)
    (fun _ location => materialized_idempotent location index GeneralBorrowFreshChild.inside)
    well bounds prepared.positions[cursor] positionValid
  simp only [membership,↓reduceIte] at outputEq
  refine ⟨outputValid,?_⟩
  rw [outputEq]
  have installed := GeneralBorrowFreshAnchor.mutable_location_owned tree index parent parentNode tag atEnd parentPresent
    (prepared.state.entries[prepared.positions[cursor]]'positionValid).data protections kind parentOwned
  rw [location_map]
  simpa only [prepared] using installed

/-- Slice-local parent ownership is transferred to the fresh child's entire
actual modified slice. The actual iterator covers every overlapping output
segment, so no allocation-wide ownership premise is used. -/
theorem ranged_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (kind : AccessKind)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent kind)
      offset.bytes (offset.bytes+len.bytes) tree.locations) :
    let changed := tree.locations.modifyRange offset len
      (fun _ location => materialized location index GeneralBorrowFreshChild.inside)
    let installed := {(GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshChild.child tag parent)) with
      locations := changed.state}
    OwnedOn (GeneralBorrowRange.LocationOwned installed protections index kind)
      offset.bytes (offset.bytes+len.bytes) changed.state := by
  dsimp only
  let prepared := tree.locations.iterMut offset len
  let modify : ByteRange → LocationTree → LocationTree :=
    fun _ location => materialized location index GeneralBorrowFreshChild.inside
  let changed := tree.locations.modifyRange offset len modify
  have sizes : changed.state.entries.size = prepared.state.entries.size := by
    dsimp only [changed,prepared]
    rw [GeneralBorrowFreshModify.state_exact tree.locations offset len modify well bounds,
      GeneralBorrowFreshModify.fold_size]
  intro position valid positive start stop
  have oldValid : position < prepared.state.entries.size := by rw [←sizes];exact valid
  obtain ⟨outputValid,entryEq⟩ := GeneralBorrowFreshModify.entry_exact tree.locations offset len modify
    (fun _ location => materialized_idempotent location index GeneralBorrowFreshChild.inside)
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
  have installed := selected_owned tree index parent parentNode tag atEnd parentPresent offset len well bounds
    protections kind owned cursor bounded
  dsimp only at installed
  rw [same] at installed
  exact installed.choose_spec

end DuplicatePrefix.GeneralBorrowFreshInstallation
#print axioms DuplicatePrefix.GeneralBorrowFreshInstallation.selected_owned

#print axioms DuplicatePrefix.GeneralBorrowFreshInstallation.ranged_owned
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshInstallation." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved slice installation dependency {dependency}"
