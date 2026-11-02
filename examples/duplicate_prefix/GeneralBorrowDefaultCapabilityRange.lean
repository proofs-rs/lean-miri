import duplicate_prefix.GeneralBorrowNormalCapabilityShape
import duplicate_prefix.GeneralBorrowDefaultMaterializedCapability
import duplicate_prefix.GeneralBorrowSharedConstructorReadFrame
namespace DuplicatePrefix.GeneralBorrowDefaultCapabilityRange
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowNodeUpdate DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.GeneralBorrowFreshInstallation
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def Parent (tree : BorrowTree) (protections : ProtectedTags) (parent : UniIndex) (location : LocationTree) : Prop :=
  Nonempty (GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) ∧
  Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location protections parent)

def Both (tree : BorrowTree) (protections : ProtectedTags) (parent child : UniIndex) (location : LocationTree) : Prop :=
  Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location protections parent) ∧
  Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location protections child)
theorem context (tree : BorrowTree) (mapping : UniKeyMap BorTag)
    (locations : DedupRangeMap LocationTree) (protections : ProtectedTags) (parent child : UniIndex) (location : LocationTree) :
    Both {tree with tagMapping := mapping,locations := locations} protections parent child location =
      Both tree protections parent child location := by
  apply propext
  constructor
  all_goals
    rintro ⟨⟨normal⟩,⟨read⟩⟩
    exact ⟨⟨⟨normal.component,normal.permissions⟩⟩,⟨⟨read.component,read.permissions⟩⟩⟩

/-- Actual selected range installation derives parent Both and fresh-child Both. All
iterator preparation, splitting and writes are included. -/
theorem append_selected_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (protections : ProtectedTags) (unprotected : protections.contains tag = false)
    (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Parent tree protections parent)
      offset.bytes (offset.bytes+len.bytes) tree.locations)
    (cursor : Nat) (valid : cursor < (tree.locations.iterMut offset len).positions.size) :
    let indexAt := (tree.locations.iterMut offset len).positions[cursor]
    let changed := tree.locations.modifyRange offset len
      (fun _ location => materialized location index GeneralBorrowFreshDefaultChild.inside)
    ∃ outputValid : indexAt < changed.state.entries.size,
      Both
        {(GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshDefaultChild.child tag parent)) with
          locations := changed.state}
        protections parent index (changed.state.entries[indexAt]'outputValid).data := by
  dsimp only
  let prepared := tree.locations.iterMut offset len
  have selected := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    (Parent tree protections parent) offset.bytes (offset.bytes+len.bytes) owned
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
  obtain ⟨forest⟩ := parentOwned.1
  obtain ⟨normal⟩ := parentOwned.2
  have installed := GeneralBorrowDefaultMaterializedCapability.append tree index parent parentNode tag atEnd parentPresent
    (prepared.state.entries[prepared.positions[cursor]]'positionValid).data protections unprotected forest normal
  rw [context]
  simpa only [prepared,Both] using installed

/-- Actual partial-range installation derives both source-specific capabilities
throughout the selected range, without permissions outside it. -/
theorem append_ranged_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (parentPresent : tree.nodeAt parent = some parentNode)
    (protections : ProtectedTags) (unprotected : protections.contains tag = false)
    (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Parent tree protections parent)
      offset.bytes (offset.bytes+len.bytes) tree.locations) :
    let changed := tree.locations.modifyRange offset len
      (fun _ location => materialized location index GeneralBorrowFreshDefaultChild.inside)
    let installed := {(GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshDefaultChild.child tag parent)) with
      locations := changed.state}
    OwnedOn (Both installed protections parent index)
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
  have installed := append_selected_owned tree index parent parentNode tag atEnd parentPresent protections unprotected offset len well bounds
    owned cursor bounded
  dsimp only at installed
  rw [same] at installed
  exact installed.choose_spec


/-- Actual selected range installation derives parent Both and fresh-child Both. All
iterator preparation, splitting and writes are included. -/
theorem reuse_selected_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (indexBound : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (parentPresent : tree.nodeAt parent = some parentNode)
    (protections : ProtectedTags) (unprotected : protections.contains tag = false)
    (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Parent tree protections parent)
      offset.bytes (offset.bytes+len.bytes) tree.locations)
    (cursor : Nat) (valid : cursor < (tree.locations.iterMut offset len).positions.size) :
    let indexAt := (tree.locations.iterMut offset len).positions[cursor]
    let changed := tree.locations.modifyRange offset len
      (fun _ location => materialized location index GeneralBorrowFreshDefaultChild.inside)
    ∃ outputValid : indexAt < changed.state.entries.size,
      Both
        {(GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshDefaultChild.child tag parent)) with
          locations := changed.state}
        protections parent index (changed.state.entries[indexAt]'outputValid).data := by
  dsimp only
  let prepared := tree.locations.iterMut offset len
  have selected := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    (Parent tree protections parent) offset.bytes (offset.bytes+len.bytes) owned
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
  obtain ⟨forest⟩ := parentOwned.1
  obtain ⟨normal⟩ := parentOwned.2
  have installed := GeneralBorrowDefaultMaterializedCapability.reuse tree index parent parentNode tag indexBound vacant fits parentPresent
    (prepared.state.entries[prepared.positions[cursor]]'positionValid).data protections unprotected forest normal
  rw [context]
  simpa only [prepared,Both] using installed

/-- Actual partial-range installation derives both source-specific capabilities
throughout the selected range, without permissions outside it. -/
theorem reuse_ranged_owned (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (indexBound : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (parentPresent : tree.nodeAt parent = some parentNode)
    (protections : ProtectedTags) (unprotected : protections.contains tag = false)
    (offset len : Size) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Parent tree protections parent)
      offset.bytes (offset.bytes+len.bytes) tree.locations) :
    let changed := tree.locations.modifyRange offset len
      (fun _ location => materialized location index GeneralBorrowFreshDefaultChild.inside)
    let installed := {(GeneralBorrowFreshGraph.attached tree index parent parentNode (GeneralBorrowFreshDefaultChild.child tag parent)) with
      locations := changed.state}
    OwnedOn (Both installed protections parent index)
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
  have installed := reuse_selected_owned tree index parent parentNode tag indexBound vacant fits parentPresent protections unprotected offset len well bounds
    owned cursor bounded
  dsimp only at installed
  rw [same] at installed
  exact installed.choose_spec

end DuplicatePrefix.GeneralBorrowDefaultCapabilityRange
