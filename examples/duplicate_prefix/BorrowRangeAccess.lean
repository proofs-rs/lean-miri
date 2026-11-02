import Lean
import duplicate_prefix.RangeMapNonempty
import duplicate_prefix.ExistingPartition
import Miri.TreeBorrows.TreeState

/-! Ranged access proofs for canonical actual Tree Borrows allocations. -/
namespace DuplicatePrefix.BorrowRangeAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open Lean Elab Tactic

private def sourceHelper (suffix : String) : CoreM Name := do
  let candidates := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match candidates with
  | [name] => pure name
  | _ => throwError "expected source helper {suffix}; found {candidates.length}"

elab "source_tree_access_at" : term => do
  return mkConst (← sourceHelper ".BorrowTree.performTreeAccessAt")

elab "source_normal_projection" : term => do
  return mkConst (← sourceHelper ".BorrowTree.normalProjection")

elab "source_min_exposed" : term => do
  return mkConst (← sourceHelper ".BorrowTree.minExposedChild")

elab "unfold_min_exposed" : tactic => do
  let name := mkIdent (← sourceHelper ".BorrowTree.minExposedChild")
  evalTactic (← `(tactic| unfold $name:ident))

elab "source_access_location" : term => do
  return mkConst (← sourceHelper ".TreeLocationAccessAtResult.location")
elab "source_access_status" : term => do
  return mkConst (← sourceHelper ".TreeLocationAccessAtResult.status")
elab "source_access_normal" : term => do
  return mkConst (← sourceHelper ".TreeLocationAccessAtResult.normalAccess")

elab "range_update_at" : term => do
  return mkConst (← sourceHelper ".DedupRangeMap.updateAt")

elab "simp_tree_helpers" : tactic => do
  let names ← [".BorrowTree.rootIndex", ".BorrowTree.performTreeAccessAt",
    ".BorrowTree.normalProjection", ".BorrowTree.traversalProjection"].mapM fun suffix => do
      return mkIdent (← sourceHelper suffix)
  let names := names.toArray
  evalTactic (← `(tactic| simp only [Id.run, bind, pure, Except.bind, Except.pure,
    $[$names:ident],*]))

def partitionWithInside {α : Type} (capacity offset finish : UInt64)
    (outside inside : α) : DedupRangeMap α :=
  if offset = 0 then
    if finish = capacity then RangeMapNonempty.homogeneous capacity inside
    else ⟨#[⟨⟨0, finish⟩, inside⟩, ⟨⟨finish, capacity⟩, outside⟩]⟩
  else
    if finish = capacity then
      ⟨#[⟨⟨0, offset⟩, outside⟩, ⟨⟨offset, capacity⟩, inside⟩]⟩
    else
      ⟨#[⟨⟨0, offset⟩, outside⟩, ⟨⟨offset, finish⟩, inside⟩,
        ⟨⟨finish, capacity⟩, outside⟩]⟩

elab "simp_range_updates" : tactic => do
  let names ← [".DedupRangeMap.segmentAt?", ".DedupRangeMap.updateAt"].mapM fun suffix => do
      return mkIdent (← sourceHelper suffix)
  let names := names.toArray
  evalTactic (← `(tactic| simp_all [DedupRangeMap.setAtPos,
    RangeMapNonempty.intervalPartition, RangeMapNonempty.intervalPosition, RangeMapNonempty.homogeneous, partitionWithInside,
    Id.run, bind, pure, Except.bind, Except.pure, $[$names:ident],*]))

theorem partition_set_same {α : Type} (capacity offset finish : UInt64) (value : α) :
    (RangeMapNonempty.intervalPartition capacity offset finish value).setAtPos
      (RangeMapNonempty.intervalPosition offset) value =
      ⟨RangeMapNonempty.intervalPartition capacity offset finish value, .ok ()⟩ := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;> simp_range_updates

theorem partition_set_replace {α : Type} (capacity offset finish : UInt64) (outside inside : α) :
    (RangeMapNonempty.intervalPartition capacity offset finish outside).setAtPos
      (RangeMapNonempty.intervalPosition offset) inside =
      ⟨partitionWithInside capacity offset finish outside inside, .ok ()⟩ := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;> simp_range_updates

theorem partition_segment {α : Type} (capacity offset finish : UInt64) (value : α) :
    range_segment_at (RangeMapNonempty.intervalPartition capacity offset finish value).entries
      (RangeMapNonempty.intervalPosition offset) = some ⟨⟨offset, finish⟩, value⟩ := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;> simp_range_updates

theorem partition_update_entry {α : Type} (capacity offset finish : UInt64) (outside inside : α) :
    range_update_at (RangeMapNonempty.intervalPartition capacity offset finish outside).entries
      (RangeMapNonempty.intervalPosition offset) ⟨⟨offset, finish⟩, inside⟩ =
      .ok (partitionWithInside capacity offset finish outside inside).entries := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;> simp_range_updates

/-- The real pure range modifier selects one split interval and applies its
callback exactly once, preserving the value outside the requested interval. -/
theorem modifyRange_new {α : Type} [DecidableEq α]
    (capacity offset len : UInt64) (value : α) (modify : ByteRange → α → α)
    (positiveLength : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    (DedupRangeMap.new (Size.ofBytes capacity) value).modifyRange
      (Size.ofBytes offset) (Size.ofBytes len) modify =
      ⟨partitionWithInside capacity offset (offset + len) value (modify ⟨offset, offset + len⟩ value),
        #[RangeMapNonempty.intervalPosition offset],
        #[⟨⟨offset, offset + len⟩, modify ⟨offset, offset + len⟩ value⟩], .ok ()⟩ := by
  have prepared :
      (DedupRangeMap.new (Size.ofBytes capacity) value).iterMutWithClone
        (Size.ofBytes offset) (Size.ofBytes len) id =
        ⟨RangeMapNonempty.intervalPartition capacity offset (offset + len) value,
          #[RangeMapNonempty.intervalPosition offset], #[⟨⟨offset, offset + len⟩, value⟩], .ok ()⟩ :=
    RangeMapNonempty.iter_mut_new_nonempty capacity offset len value positiveLength bounds
  unfold DedupRangeMap.modifyRange DedupRangeMap.modifyRangeWithClone
  rw [prepared]
  dsimp only
  simp only [← Array.forIn_toList]
  simp [partition_segment, partition_update_entry, Id.run, bind, pure, Except.bind, Except.pure]

theorem modifyRange_intervalPartition {α : Type} [DecidableEq α]
    (capacity offset len : UInt64) (value : α) (modify : ByteRange → α → α)
    (positiveLength : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    (RangeMapNonempty.intervalPartition capacity offset (offset + len) value).modifyRange
      (Size.ofBytes offset) (Size.ofBytes len) modify =
      ⟨partitionWithInside capacity offset (offset + len) value (modify ⟨offset, offset + len⟩ value),
        #[RangeMapNonempty.intervalPosition offset],
        #[⟨⟨offset, offset + len⟩, modify ⟨offset, offset + len⟩ value⟩], .ok ()⟩ := by
  have prepared :
      (RangeMapNonempty.intervalPartition capacity offset (offset + len) value).iterMutWithClone
        (Size.ofBytes offset) (Size.ofBytes len) id =
        ⟨RangeMapNonempty.intervalPartition capacity offset (offset + len) value,
          #[RangeMapNonempty.intervalPosition offset], #[⟨⟨offset, offset + len⟩, value⟩], .ok ()⟩ :=
    ExistingPartition.iterMut_intervalPartition capacity offset len value positiveLength bounds
  unfold DedupRangeMap.modifyRange DedupRangeMap.modifyRangeWithClone
  rw [prepared]
  dsimp only
  simp only [← Array.forIn_toList]
  simp [partition_segment, partition_update_entry, Id.run, bind, pure, Except.bind, Except.pure]

abbrev rootLocation : LocationTree :=
  ⟨⟨#[some ⟨.Unique, true, .None⟩]⟩, {}⟩

theorem new_locations (tag : BorTag) (size : Size) :
    (BorrowTree.new tag size).locations = DedupRangeMap.new size rootLocation := by rfl

theorem new_root_index (tag : BorTag) (size : Size) :
    (BorrowTree.new tag size).indexOfTag tag = some ⟨0⟩ := by
  simp [BorrowTree.new, BorrowTree.indexOfTag, UniKeyMap.get, Id.run]
  simp_tree_helpers
  simp [Array.find?_singleton]

abbrev rootNormal : Tree.NormalTreeState := {
  topology := ⟨#[⟨none, []⟩]⟩
  defaultStates := #[⟨.Disabled, false, .None⟩]
  protectedNodes := []
  locationStates := #[some ⟨.Unique, true, .None⟩]
}

theorem root_normal_projection (tag : BorTag) (size : Size) :
    source_normal_projection (BorrowTree.new tag size) rootLocation {} = rootNormal := by
  simp_tree_helpers
  simp [BorrowTree.new, rootLocation, rootNormal, UniValMap.insert, UniValMap.extendTo,
    UniValMap.get, UniValMap.entries, UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    ProtectedTags.contains, ProtectedTags.get, Permission.newDisabled, Permission.newUnique,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp_tree_helpers
  simp [Id.run, rootNormal, UniIndex.toNat, bind, pure]

theorem root_normal_access (kind : AccessKind) :
    rootNormal.performAccess 0 kind .VisitChildrenOfAccessed =
      ⟨rootNormal, 0, [⟨0, .LocalAccess⟩], .Completed⟩ := by
  cases kind <;> decide

abbrev rootAccess (tag : BorTag) (size : Size) (kind : AccessKind) (range : ByteRange) :=
  source_tree_access_at (BorrowTree.new tag size) rootLocation (some ⟨0⟩) kind {}
    Tree.ChildrenVisitMode.VisitChildrenOfAccessed range

theorem root_access_local (tag : BorTag) (size : Size) (kind : AccessKind) (range : ByteRange) :
    source_access_location (rootAccess tag size kind range) = rootLocation ∧
    source_access_status (rootAccess tag size kind range) = none := by
  unfold rootAccess
  simp_tree_helpers
  simp only [BorrowTree.performNormalAccessAt, root_normal_projection, UniIndex.toNat, root_normal_access]
  simp [rootNormal, rootLocation, BorrowTree.new, BorrowTree.nodeAt, UniValMap.insert, UniValMap.extendTo,
    UniValMap.get, UniValMap.entries, UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    ProtectedTags.contains, ProtectedTags.get, Permission.newDisabled, Permission.newUnique,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp_tree_helpers
  simp only [root_normal_access]
  simp [Id.run, UniIndex.toNat, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
    BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem root_nonempty_range_access (tag : BorTag)
    (capacity offset len : UInt64) (kind : AccessKind)
    (positiveLength : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    ((BorrowTree.new tag (Size.ofBytes capacity)).performBorrowAccessRange
      (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len) kind {}
      .VisitChildrenOfAccessed).status = .Completed := by
  have accessFact := root_access_local tag (Size.ofBytes capacity) kind ⟨offset, offset + len⟩
  unfold BorrowTree.performBorrowAccessRange
  dsimp only
  rw [new_root_index]
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  rw [new_locations, RangeMapNonempty.iter_mut_new_nonempty capacity offset len rootLocation
    positiveLength bounds]
  simp [accessFact.1, accessFact.2, partition_set_same, Id.run, bind, pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem root_nonempty_range_tree (tag : BorTag)
    (capacity offset len : UInt64) (kind : AccessKind)
    (positiveLength : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    ((BorrowTree.new tag (Size.ofBytes capacity)).performBorrowAccessRange
      (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len) kind {}
      .VisitChildrenOfAccessed).tree =
      { BorrowTree.new tag (Size.ofBytes capacity) with
        locations := RangeMapNonempty.intervalPartition capacity offset (offset + len) rootLocation } := by
  have accessFact := root_access_local tag (Size.ofBytes capacity) kind ⟨offset, offset + len⟩
  unfold BorrowTree.performBorrowAccessRange
  dsimp only
  rw [new_root_index]
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  rw [new_locations, RangeMapNonempty.iter_mut_new_nonempty capacity offset len rootLocation
    positiveLength bounds]
  simp [accessFact.1, accessFact.2, partition_set_same, Id.run, bind, pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

abbrev childLocation (written : Bool) : LocationTree :=
  ⟨⟨#[some ⟨.Unique, true, .None⟩,
      some ⟨if written then .Unique else .ReservedFrz false, true, .None⟩]⟩, {}⟩

abbrev canonicalChildTree (rootTag childTag : BorTag)
    (locations : DedupRangeMap LocationTree) : BorrowTree := {
  tagMapping := { mapping := #[(rootTag, ⟨0⟩), (childTag, ⟨1⟩)] }
  nodes := { data := #[
    some { tag := rootTag, parent := none, children := #[⟨1⟩], defaultInitialPermission := .Disabled, defaultInitialSifa := .None },
    some { tag := childTag, parent := some ⟨0⟩, children := #[], defaultInitialPermission := .ReservedFrz false, defaultInitialSifa := .None }] }
  locations
  roots := #[⟨0⟩]
}

theorem canonical_child_index (rootTag childTag : BorTag)
    (locations : DedupRangeMap LocationTree) (distinct : rootTag ≠ childTag) :
    (canonicalChildTree rootTag childTag locations).indexOfTag childTag = some ⟨1⟩ := by
  simp only [BorrowTree.indexOfTag, canonicalChildTree, UniKeyMap.get]
  rw [← Array.find?_toList]
  simp [distinct, Ne.symm distinct]

theorem canonical_child_locations (rootTag childTag : BorTag)
    (locations : DedupRangeMap LocationTree) :
    (canonicalChildTree rootTag childTag locations).locations = locations := by rfl

abbrev childProtected (tag : BorTag) : ProtectedTags := ⟨#[(tag, .StrongProtector)]⟩

abbrev childNormal (written : Bool) : Tree.NormalTreeState := {
  topology := ⟨#[⟨none, [1]⟩, ⟨some 0, []⟩]⟩
  defaultStates := #[⟨.Disabled, false, .None⟩, ⟨.ReservedFrz false, false, .None⟩]
  protectedNodes := [1]
  locationStates := #[some ⟨.Unique, true, .None⟩,
    some ⟨if written then .Unique else .ReservedFrz false, true, .None⟩]
}

theorem child_normal_projection (rootTag childTag : BorTag)
    (locations : DedupRangeMap LocationTree) (written : Bool) (distinct : rootTag ≠ childTag) :
    source_normal_projection (canonicalChildTree rootTag childTag locations)
      (childLocation written) (childProtected childTag) = childNormal written := by
  simp_tree_helpers
  simp [canonicalChildTree, childLocation, childNormal, childProtected,
    UniValMap.get, UniValMap.entries, UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    ProtectedTags.contains, ProtectedTags.get, Array.find?_singleton, distinct, Ne.symm distinct,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp [List.range'_succ, List.range'_zero, distinct, Ne.symm distinct, Id.run, bind, pure]

theorem child_normal_access (written : Bool) (kind : AccessKind) (mode : Tree.ChildrenVisitMode) :
    (childNormal written).performAccess 1 kind mode =
      ⟨childNormal (written || kind == .Write), 0,
        [⟨1, .LocalAccess⟩, ⟨0, .LocalAccess⟩], .Completed⟩ := by
  cases written <;> cases kind <;> cases mode <;> decide

theorem canonical_min_exposed (rootTag childTag : BorTag)
    (locations : DedupRangeMap LocationTree) :
    source_min_exposed (canonicalChildTree rootTag childTag locations) ⟨1⟩ = none := by
  unfold_min_exposed
  simp only [Id.run, bind, pure, ForIn.forIn, Lean.instForInLoopUnitOfMonad]
  name_range_scan
  have first : scan () (none, #[⟨1⟩], 0, none) =
      .yield (none, #[], 1, none) := by
    simp [scan, UniValMap.size, UniValMap.get, UniIndex.toNat, bind, pure,
      ← Array.forIn_toList]
  have last : scan () (none, #[], 1, none) = .done (none, #[], 1, none) := by
    simp [scan, UniValMap.size, bind, pure]
  have loopDone := RangeMapNonempty.loop_one_update scan _ _ first last
  simp [loopDone, Id.run, bind, pure]

abbrev childAccess (rootTag childTag : BorTag) (locations : DedupRangeMap LocationTree)
    (written : Bool) (kind : AccessKind) (range : ByteRange) :=
  source_tree_access_at (canonicalChildTree rootTag childTag locations) (childLocation written)
    (some ⟨1⟩) kind (childProtected childTag) .VisitChildrenOfAccessed range

theorem child_access_local (rootTag childTag : BorTag) (locations : DedupRangeMap LocationTree)
    (written : Bool) (kind : AccessKind) (range : ByteRange) (distinct : rootTag ≠ childTag) :
    source_access_location (childAccess rootTag childTag locations written kind range) =
      childLocation (written || kind == .Write) ∧
    source_access_status (childAccess rootTag childTag locations written kind range) = none := by
  unfold childAccess
  simp_tree_helpers
  simp only [BorrowTree.performNormalAccessAt,
    child_normal_projection rootTag childTag locations written distinct, UniIndex.toNat, child_normal_access]
  simp [canonicalChildTree, childLocation, childNormal, childProtected,
    BorrowTree.nodeAt, UniValMap.insert, UniValMap.extendTo, UniValMap.get, UniValMap.entries,
    UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    ProtectedTags.contains, ProtectedTags.get, Array.find?_singleton, distinct, Ne.symm distinct,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp_tree_helpers
  simp only [child_normal_access]
  simp [Id.run, UniIndex.toNat, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
    BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]

theorem child_nonempty_range_access (rootTag childTag : BorTag)
    (capacity offset len : UInt64) (written : Bool) (kind : AccessKind)
    (distinct : rootTag ≠ childTag)
    (positiveLength : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    ((canonicalChildTree rootTag childTag (DedupRangeMap.new (Size.ofBytes capacity) (childLocation written))).performBorrowAccessRange (.concrete childTag) (Size.ofBytes offset) (Size.ofBytes len)
        kind (childProtected childTag) .VisitChildrenOfAccessed).status = .Completed := by
  have accessFact := child_access_local rootTag childTag
    (DedupRangeMap.new (Size.ofBytes capacity) (childLocation written)) written kind
    ⟨offset, offset + len⟩ distinct
  unfold BorrowTree.performBorrowAccessRange
  dsimp only
  rw [canonical_child_index rootTag childTag _ distinct]
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  rw [RangeMapNonempty.iter_mut_new_nonempty capacity offset len (childLocation written)
      positiveLength bounds]
  simp [accessFact.1, accessFact.2, partition_set_replace, Id.run, bind, pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem child_nonempty_range_tree (rootTag childTag : BorTag)
    (capacity offset len : UInt64) (written : Bool) (kind : AccessKind)
    (distinct : rootTag ≠ childTag)
    (positiveLength : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    ((canonicalChildTree rootTag childTag (DedupRangeMap.new (Size.ofBytes capacity) (childLocation written))).performBorrowAccessRange (.concrete childTag) (Size.ofBytes offset) (Size.ofBytes len)
        kind (childProtected childTag) .VisitChildrenOfAccessed).tree =
      canonicalChildTree rootTag childTag
        (partitionWithInside capacity offset (offset + len) (childLocation written)
          (childLocation (written || kind == .Write))) := by
  have accessFact := child_access_local rootTag childTag
    (DedupRangeMap.new (Size.ofBytes capacity) (childLocation written)) written kind
    ⟨offset, offset + len⟩ distinct
  unfold BorrowTree.performBorrowAccessRange
  dsimp only
  rw [canonical_child_index rootTag childTag _ distinct]
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  rw [RangeMapNonempty.iter_mut_new_nonempty capacity offset len (childLocation written)
      positiveLength bounds]
  simp [accessFact.1, accessFact.2, partition_set_replace, Id.run, bind, pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

abbrev childAccessMode (rootTag childTag : BorTag) (locations : DedupRangeMap LocationTree)
    (written : Bool) (kind : AccessKind) (mode : Tree.ChildrenVisitMode) (range : ByteRange) :=
  source_tree_access_at (canonicalChildTree rootTag childTag locations) (childLocation written)
    (some ⟨1⟩) kind (childProtected childTag) mode range

theorem child_access_local_mode (rootTag childTag : BorTag) (locations : DedupRangeMap LocationTree)
    (written : Bool) (kind : AccessKind) (mode : Tree.ChildrenVisitMode) (range : ByteRange)
    (distinct : rootTag ≠ childTag) :
    source_access_location (childAccessMode rootTag childTag locations written kind mode range) =
      childLocation (written || kind == .Write) ∧
    source_access_status (childAccessMode rootTag childTag locations written kind mode range) = none := by
  unfold childAccessMode
  simp_tree_helpers
  simp only [BorrowTree.performNormalAccessAt,
    child_normal_projection rootTag childTag locations written distinct, UniIndex.toNat, child_normal_access]
  simp [canonicalChildTree, childLocation, childNormal, childProtected, canonical_min_exposed,
    BorrowTree.nodeAt, UniValMap.insert, UniValMap.extendTo, UniValMap.get, UniValMap.entries,
    UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    ProtectedTags.contains, ProtectedTags.get, Array.find?_singleton, distinct, Ne.symm distinct,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp_tree_helpers
  try simp only [child_normal_access, canonical_min_exposed]
  simp [Id.run, UniIndex.toNat, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
    BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero, canonical_min_exposed]

#print axioms root_normal_projection
#print axioms root_normal_access
#print axioms root_access_local
#print axioms partition_set_same
#print axioms root_nonempty_range_access
#print axioms root_nonempty_range_tree
#print axioms child_normal_projection
#print axioms child_normal_access
#print axioms partition_set_replace
#print axioms partition_segment
#print axioms child_access_local
#print axioms partition_update_entry
#print axioms modifyRange_new
#print axioms canonical_child_index
#print axioms child_nonempty_range_access
#print axioms child_nonempty_range_tree
#print axioms canonical_min_exposed
#print axioms child_access_local_mode
#print axioms modifyRange_intervalPartition

end DuplicatePrefix.BorrowRangeAccess
