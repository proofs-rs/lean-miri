import duplicate_prefix.NestedConstruction
import duplicate_prefix.NestedRelease

namespace DuplicatePrefix.NestedTransitions
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open BorrowRangeAccess RangeMapNonempty NestedBorrowAccess NestedConstruction
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

abbrev extraProtected (tags : Fin 6 → BorTag) (extra : Fin 6) : ProtectedTags :=
  ⟨#[(tags 1, .StrongProtector), (tags extra, .StrongProtector)]⟩
abbrev normal3 (read : Bool) : Tree.NormalTreeState := {
  topology := ⟨#[⟨none, [1]⟩, ⟨some 0, [2]⟩, ⟨some 1, []⟩]⟩
  defaultStates := #[⟨.Disabled, false, .None⟩, ⟨.ReservedFrz false, false, .None⟩, ⟨.Frozen, false, .Read⟩]
  protectedNodes := [1]
  locationStates := (location3 read).perms.data
}
abbrev normal4 (released isProtected : Bool) : Tree.NormalTreeState := {
  topology := ⟨#[⟨none, [1]⟩, ⟨some 0, [2]⟩, ⟨some 1, [3]⟩, ⟨some 2, []⟩]⟩
  defaultStates := #[⟨.Disabled, false, .None⟩, ⟨.ReservedFrz false, false, .None⟩,
    ⟨.Frozen, false, .Read⟩, ⟨.Frozen, false, .Read⟩]
  protectedNodes := if isProtected then [1, 3] else [1]
  locationStates := (location4 released).perms.data
}
abbrev normal5 (read : Bool) : Tree.NormalTreeState := {
  topology := ⟨#[⟨none, [1]⟩, ⟨some 0, [2, 4]⟩, ⟨some 1, [3]⟩, ⟨some 2, []⟩, ⟨some 1, []⟩]⟩
  defaultStates := #[⟨.Disabled, false, .None⟩, ⟨.ReservedFrz false, false, .None⟩,
    ⟨.Frozen, false, .Read⟩, ⟨.Frozen, false, .Read⟩, ⟨.ReservedFrz false, false, .Read⟩]
  protectedNodes := [1]
  locationStates := (location5 read).perms.data
}

theorem normal3_read (read : Bool) :
    (normal3 read).performAccess 2 .Read .VisitChildrenOfAccessed =
      ⟨normal3 true, 0, [⟨2, .LocalAccess⟩, ⟨1, .LocalAccess⟩, ⟨0, .LocalAccess⟩], .Completed⟩ := by
  cases read <;> decide

theorem normal4_parent_read :
    (normal4 true false).performAccess 1 .Read .VisitChildrenOfAccessed =
      ⟨normal4 true false, 0, [⟨1, .LocalAccess⟩, ⟨0, .LocalAccess⟩], .Completed⟩ := by decide

theorem normal4_release (released : Bool) :
    (normal4 released true).performAccess 3 .Read .SkipChildrenOfAccessed =
      ⟨normal4 true true, 0, [⟨3, .LocalAccess⟩, ⟨2, .LocalAccess⟩, ⟨1, .LocalAccess⟩, ⟨0, .LocalAccess⟩], .Completed⟩ := by
  cases released <;> decide

theorem normal5_read (read : Bool) :
    (normal5 read).performAccess 4 .Read .VisitChildrenOfAccessed =
      ⟨normal5 true, 0, [⟨4, .LocalAccess⟩, ⟨1, .LocalAccess⟩, ⟨0, .LocalAccess⟩], .Completed⟩ := by
  cases read <;> decide

theorem projection3 (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) (read : Bool) :
    source_normal_projection (tree3 tags locations) (location3 read) (extraProtected tags 3) = normal3 read := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp_tree_helpers
  simp [tree3, stageNode, location3, location4, location5, normal3, normal4, normal5,
    extraProtected, nestedProtected, childProtected, mutableNone, mutableRead, frozenRead, frozenNone,
    UniValMap.get, UniValMap.entries, UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    ProtectedTags.contains, ProtectedTags.get, ← Array.find?_toList, eqTags,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero, Id.run]

theorem projection4 (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) :
    source_normal_projection (tree4 tags locations) (location4 true) (nestedProtected tags) = normal4 true false := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp_tree_helpers
  simp [tree4, stageNode, location3, location4, location5, normal3, normal4, normal5,
    extraProtected, nestedProtected, childProtected, mutableNone, mutableRead, frozenRead, frozenNone,
    UniValMap.get, UniValMap.entries, UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    ProtectedTags.contains, ProtectedTags.get, ← Array.find?_toList, eqTags,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero, Id.run]

theorem projection5 (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) (read : Bool) :
    source_normal_projection (tree5 tags locations) (location5 read) (extraProtected tags 5) = normal5 read := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp_tree_helpers
  simp [tree5, stageNode, location3, location4, location5, normal3, normal4, normal5,
    extraProtected, nestedProtected, childProtected, mutableNone, mutableRead, frozenRead, frozenNone,
    UniValMap.get, UniValMap.entries, UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    ProtectedTags.contains, ProtectedTags.get, ← Array.find?_toList, eqTags,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero, Id.run]

theorem projection4_release (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) (released : Bool) :
    source_normal_projection (tree4 tags locations) (location4 released) (extraProtected tags 3) =
      normal4 released true := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp_tree_helpers
  simp [tree4, stageNode, location4, normal4, extraProtected, mutableNone, frozenRead, frozenNone,
    UniValMap.get, UniValMap.entries, UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    ProtectedTags.contains, ProtectedTags.get, ← Array.find?_toList, eqTags,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero, Id.run]

theorem min_exposed4 (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree) :
    source_min_exposed (tree4 tags locations) ⟨3⟩ = none := by
  unfold_min_exposed
  simp only [Id.run, bind, pure, ForIn.forIn, Lean.instForInLoopUnitOfMonad]
  name_range_scan
  have first : scan () (none, #[⟨3⟩], 0, none) = .yield (none, #[], 1, none) := by
    simp [scan, UniValMap.size, UniValMap.get, UniIndex.toNat, bind, pure, ← Array.forIn_toList]
  have last : scan () (none, #[], 1, none) = .done (none, #[], 1, none) := by
    simp [scan, UniValMap.size, bind, pure]
  have final := loop_one_update scan _ _ first last
  simp [final, Id.run, bind, pure]

abbrev access3 (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree) (read : Bool) (range : ByteRange) :=
  source_tree_access_at (tree3 tags locations) (location3 read) (some ⟨2⟩) .Read
    (extraProtected tags 3) .VisitChildrenOfAccessed range

theorem access3_local (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) (read : Bool) (range : ByteRange) :
    source_access_location (access3 tags locations read range) = location3 true ∧
    source_access_status (access3 tags locations read range) = none := by
  unfold access3
  simp_tree_helpers
  simp only [BorrowTree.performNormalAccessAt, projection3 tags distinct locations read,
    show (⟨2⟩ : UniIndex).toNat = 2 from rfl, normal3_read]
  simp [tree3, stageNode, location3, location4, location5, normal3, normal4, normal5,
    mutableNone, mutableRead, frozenRead, frozenNone, min_exposed4,
    BorrowTree.nodeAt, UniValMap.get, UniValMap.entries,
    UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]
  simp_tree_helpers
  simp [min_exposed4, Id.run, UniIndex.toNat, UniIndex.ofNat?, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
    BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]

abbrev access4 (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree) (range : ByteRange) :=
  source_tree_access_at (tree4 tags locations) (location4 true) (some ⟨1⟩) .Read
    (nestedProtected tags) .VisitChildrenOfAccessed range

theorem access4_local (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) (range : ByteRange) :
    source_access_location (access4 tags locations range) = location4 true ∧
    source_access_status (access4 tags locations range) = none := by
  unfold access4
  simp_tree_helpers
  simp only [BorrowTree.performNormalAccessAt, projection4 tags distinct locations,
    show (⟨1⟩ : UniIndex).toNat = 1 from rfl, normal4_parent_read]
  simp [tree4, stageNode, location3, location4, location5, normal3, normal4, normal5,
    mutableNone, mutableRead, frozenRead, frozenNone, min_exposed4,
    BorrowTree.nodeAt, UniValMap.get, UniValMap.entries,
    UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]
  simp_tree_helpers
  simp [min_exposed4, Id.run, UniIndex.toNat, UniIndex.ofNat?, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
    BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]

abbrev access5 (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree) (read : Bool) (range : ByteRange) :=
  source_tree_access_at (tree5 tags locations) (location5 read) (some ⟨4⟩) .Read
    (extraProtected tags 5) .VisitChildrenOfAccessed range

theorem access5_local (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) (read : Bool) (range : ByteRange) :
    source_access_location (access5 tags locations read range) = location5 true ∧
    source_access_status (access5 tags locations read range) = none := by
  unfold access5
  simp_tree_helpers
  simp only [BorrowTree.performNormalAccessAt, projection5 tags distinct locations read,
    show (⟨4⟩ : UniIndex).toNat = 4 from rfl, normal5_read]
  simp [tree5, stageNode, location3, location4, location5, normal3, normal4, normal5,
    mutableNone, mutableRead, frozenRead, frozenNone, min_exposed4,
    BorrowTree.nodeAt, UniValMap.get, UniValMap.entries,
    UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]
  simp_tree_helpers
  simp [min_exposed4, Id.run, UniIndex.toNat, UniIndex.ofNat?, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
    BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]

abbrev access4release (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree) (read : Bool) (range : ByteRange) :=
  source_tree_access_at (tree4 tags locations) (location4 read) (some ⟨3⟩) .Read
    (extraProtected tags 3) .SkipChildrenOfAccessed range

theorem access4release_local (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) (read : Bool) (range : ByteRange) :
    source_access_location (access4release tags locations read range) = location4 true ∧
    source_access_status (access4release tags locations read range) = none := by
  unfold access4release
  simp_tree_helpers
  simp only [BorrowTree.performNormalAccessAt, projection4_release tags distinct locations read,
    show (⟨3⟩ : UniIndex).toNat = 3 from rfl, normal4_release]
  simp [tree4, stageNode, location3, location4, location5, normal3, normal4, normal5,
    mutableNone, mutableRead, frozenRead, frozenNone, min_exposed4,
    BorrowTree.nodeAt, UniValMap.get, UniValMap.entries,
    UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]
  simp_tree_helpers
  simp [min_exposed4, Id.run, UniIndex.toNat, UniIndex.ofNat?, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
    BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]

private theorem partition_set_middle (capacity offset finish : UInt64)
    (outside inside replacement : LocationTree) :
    (partitionWithInside capacity offset finish outside inside).setAtPos (intervalPosition offset) replacement =
      ⟨partitionWithInside capacity offset finish outside replacement, .ok ()⟩ := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_range_updates <;> simp_all [partitionWithInside, intervalPosition, homogeneous]

private theorem range_once (tree : BorrowTree) (tag : BorTag) (index : UniIndex)
    (capacity offset len : UInt64) (outside inside replacement : LocationTree)
    (kind : AccessKind) (protections : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (locations : tree.locations = partitionWithInside capacity offset (offset + len) outside inside)
    (lookup : tree.indexOfTag tag = some index)
    (positive : (0 : UInt64) < len) (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (localFact :
      source_access_location (source_tree_access_at tree inside (some index) kind protections mode ⟨offset, offset + len⟩) = replacement ∧
      source_access_status (source_tree_access_at tree inside (some index) kind protections mode ⟨offset, offset + len⟩) = none) :
    let result := tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len) kind protections mode
    result.status = .Completed ∧ result.tree =
      {tree with locations := partitionWithInside capacity offset (offset + len) outside replacement} := by
  dsimp only
  unfold BorrowTree.performBorrowAccessRange
  dsimp only
  rw [lookup]
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  rw [locations, iterMut_partition capacity offset len outside inside positive bounds]
  simp [localFact.1, localFact.2, partition_set_middle, Id.run, bind, pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem parent_read3 (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset len : UInt64) (read : Bool)
    (positive : (0 : UInt64) < len) (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    let initial := tree3 tags (partitionWithInside capacity offset (offset + len) rootLocation (location3 read))
    let result := initial.performBorrowAccessRange (.concrete (tags 2))
      (Size.ofBytes offset) (Size.ofBytes len) .Read (extraProtected tags 3) .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree =
      tree3 tags (partitionWithInside capacity offset (offset + len) rootLocation (location3 true)) := by
  let locations := partitionWithInside capacity offset (offset + len) rootLocation (location3 read)
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  have lookup : (tree3 tags locations).indexOfTag (tags 2) = some ⟨2⟩ := by
    simp [BorrowTree.indexOfTag, tree3, UniKeyMap.get, ← Array.find?_toList, eqTags]
  have fact := range_once (tree3 tags locations) (tags 2) ⟨2⟩ capacity offset len
    rootLocation (location3 read) (location3 true) .Read (extraProtected tags 3) .VisitChildrenOfAccessed rfl lookup
    positive bounds (access3_local tags distinct locations read ⟨offset, offset + len⟩)
  simpa [locations, tree3] using fact

#print axioms parent_read3
theorem parent_read4 (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset len : UInt64)
    (positive : (0 : UInt64) < len) (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    let initial := tree4 tags (partitionWithInside capacity offset (offset + len) rootLocation (location4 true))
    let result := initial.performBorrowAccessRange (.concrete (tags 1))
      (Size.ofBytes offset) (Size.ofBytes len) .Read (nestedProtected tags) .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree =
      tree4 tags (partitionWithInside capacity offset (offset + len) rootLocation (location4 true)) := by
  let locations := partitionWithInside capacity offset (offset + len) rootLocation (location4 true)
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  have lookup : (tree4 tags locations).indexOfTag (tags 1) = some ⟨1⟩ := by
    simp [BorrowTree.indexOfTag, tree4, UniKeyMap.get, ← Array.find?_toList, eqTags]
  have fact := range_once (tree4 tags locations) (tags 1) ⟨1⟩ capacity offset len
    rootLocation (location4 true) (location4 true) .Read (nestedProtected tags) .VisitChildrenOfAccessed rfl lookup
    positive bounds (access4_local tags distinct locations ⟨offset, offset + len⟩)
  simpa [locations, tree4] using fact

#print axioms parent_read4
theorem parent_read5 (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset len : UInt64) (read : Bool)
    (positive : (0 : UInt64) < len) (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    let initial := tree5 tags (partitionWithInside capacity offset (offset + len) rootLocation (location5 read))
    let result := initial.performBorrowAccessRange (.concrete (tags 4))
      (Size.ofBytes offset) (Size.ofBytes len) .Read (extraProtected tags 5) .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree =
      tree5 tags (partitionWithInside capacity offset (offset + len) rootLocation (location5 true)) := by
  let locations := partitionWithInside capacity offset (offset + len) rootLocation (location5 read)
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  have lookup : (tree5 tags locations).indexOfTag (tags 4) = some ⟨4⟩ := by
    simp [BorrowTree.indexOfTag, tree5, UniKeyMap.get, ← Array.find?_toList, eqTags]
  have fact := range_once (tree5 tags locations) (tags 4) ⟨4⟩ capacity offset len
    rootLocation (location5 read) (location5 true) .Read (extraProtected tags 5) .VisitChildrenOfAccessed rfl lookup
    positive bounds (access5_local tags distinct locations read ⟨offset, offset + len⟩)
  simpa [locations, tree5] using fact

#print axioms parent_read5
theorem parent_read2 (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset len : UInt64) (positive : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    let initial := tree2 tags (partitionWithInside capacity offset (offset + len) rootLocation (childLocation false))
    let result := initial.performBorrowAccessRange (.concrete (tags 1))
      (Size.ofBytes offset) (Size.ofBytes len) .Read (nestedProtected tags) .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = initial := by
  let locations := partitionWithInside capacity offset (offset + len) rootLocation (childLocation false)
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  have distinct01 : tags 0 ≠ tags 1 := by simp [eqTags]
  have lookup := canonical_child_index (tags 0) (tags 1) locations distinct01
  have localFact := child_access_local (tags 0) (tags 1) locations false .Read ⟨offset, offset + len⟩ distinct01
  have readNotWrite : (AccessKind.Read == AccessKind.Write) = false := by decide
  simp only [readNotWrite, Bool.false_or] at localFact
  have fact := range_once (tree2 tags locations) (tags 1) ⟨1⟩ capacity offset len
    rootLocation (childLocation false) (childLocation false) .Read (nestedProtected tags)
    .VisitChildrenOfAccessed rfl lookup positive bounds localFact
  simpa [locations, tree2, canonicalChildTree] using fact

theorem index4_release (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) :
    (tree4 tags locations).indexOfTag (tags 3) = some ⟨3⟩ := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp [BorrowTree.indexOfTag, tree4, UniKeyMap.get, ← Array.find?_toList, eqTags]

theorem exposure4_release (tags : Fin 6 → BorTag)
    (locations : DedupRangeMap LocationTree) (distinct : Function.Injective tags) :
    (tree4 tags locations).updateExposureForProtectorRelease (tags 3) = ⟨tree4 tags locations, .ok ()⟩ := by
  unfold BorrowTree.updateExposureForProtectorRelease
  dsimp only
  rw [index4_release tags distinct locations]
  simp [BorrowTree.nodeAt, UniValMap.get, UniIndex.toNat, Id.run, pure]

private theorem release4_single (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (before after : Option ByteRange) (source : ByteRange) (released : Bool) :
    let initial := MixedRelease.withOutside before after #[⟨source, location4 released⟩]
    let final := MixedRelease.withOutside before after #[⟨source, location4 true⟩]
    (tree4 tags initial).releaseProtector (tags 3) (extraProtected tags 3) =
      ⟨tree4 tags final, .Released⟩ := by
  dsimp only
  let locations := MixedRelease.withOutside before after #[⟨source, location4 released⟩]
  have readLocation (range : ByteRange) := (access4release_local tags distinct locations released range).1
  have readStatus (range : ByteRange) := (access4release_local tags distinct locations released range).2
  simp only [access4release] at readLocation readStatus
  change (tree4 tags locations).releaseProtector _ _ = _
  unfold BorrowTree.releaseProtector
  dsimp only
  rw [index4_release tags distinct locations]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  cases before <;> cases after <;> cases released
  all_goals
    first
    | have locSize : locations.entries.size = 1 := by simp [locations, MixedRelease.withOutside]
    | have locSize : locations.entries.size = 2 := by simp [locations, MixedRelease.withOutside]
    | have locSize : locations.entries.size = 3 := by simp [locations, MixedRelease.withOutside]
    simp only [locSize, Nat.sub_zero, Nat.add_sub_cancel, List.range'_succ, List.range'_zero]
    simp only [locations, MixedRelease.withOutside] at *
    simp only [Option.toArray_none, Option.toArray_some, Array.map_empty, Array.map_singleton,
      Array.empty_append, Array.append_empty, Array.append_assoc] at *
    simp [readLocation, readStatus, UniValMap.get, UniIndex.toNat, Permission.associatedAccess, Id.run, bind, pure]
    try simp_release_set
    try simp [exposure4_release, distinct]

theorem len_helper_release (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset finish : UInt64) (released : Bool) :
    (tree4 tags (partitionWithInside capacity offset finish rootLocation (location4 released))).releaseProtector
      (tags 3) (extraProtected tags 3) =
      ⟨tree4 tags (partitionWithInside capacity offset finish rootLocation (location4 true)), .Released⟩ := by
  have release := release4_single tags distinct
    (if offset = 0 then none else some ⟨0, offset⟩)
    (if finish = capacity then none else some ⟨finish, capacity⟩)
    ⟨offset, finish⟩ released
  dsimp only at release ⊢
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_all [partitionWithInside, homogeneous, MixedRelease.withOutside]

#print axioms parent_read2
#print axioms len_helper_release
#print axioms normal3_read
#print axioms normal4_parent_read
#print axioms normal4_release
#print axioms normal5_read
end DuplicatePrefix.NestedTransitions

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.NestedTransitions.parent_read2,
      ``DuplicatePrefix.NestedTransitions.parent_read3, ``DuplicatePrefix.NestedTransitions.parent_read4,
      ``DuplicatePrefix.NestedTransitions.parent_read5, ``DuplicatePrefix.NestedTransitions.len_helper_release] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
