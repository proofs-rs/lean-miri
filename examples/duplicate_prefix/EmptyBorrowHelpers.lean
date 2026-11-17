import duplicate_prefix.NestedConstruction
import duplicate_prefix.ProtectedStages
import duplicate_prefix.RangeMapProof

/-! Empty-slice helper borrows execute the actual zero-length paths. Offset
and allocation capacity are unrestricted here; no inside permission is
materialized, including at a one-past pointer. -/
namespace DuplicatePrefix.EmptyBorrowHelpers
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open BorrowRangeAccess RangeMapNonempty NestedBorrowAccess NestedConstruction NestedTransitions
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

private theorem sifa3_empty (tags : Fin 6 → BorTag) (capacity : UInt64) :
    let tree := tree3 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
    source_sifa_update tree ⟨1⟩ .Read = (tree, .ok ()) := by
  let tree := tree3 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
  change source_sifa_update tree ⟨1⟩ .Read = (tree, .ok ())
  unfold_sifa
  simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte, ForIn.forIn]
  name_range_scan
  have first : scan () (none, tree, some (⟨1⟩ : UniIndex), 0, true) =
      .yield (none, tree, some (⟨1⟩ : UniIndex), 0, false) := by
    by_cases empty : capacity = 0 <;>
      simp [scan, tree, tree3, stageNode, rootLocation, empty, UniValMap.get,
        UniValMap.insert, UniValMap.extendTo, UniValMap.size, UniIndex.toNat,
        DedupRangeMap.new, DedupRangeMap.iterAll, DedupRangeMap.modifyAll, Size.ofBytes,
        IdempotentForeignAccess.ensureNoStrongerThan, IdempotentForeignAccess.rank, Id.run, bind, pure]
  have last : scan () (none, tree, some (⟨1⟩ : UniIndex), 0, false) =
      .done (none, tree, some (⟨1⟩ : UniIndex), 0, false) := by
    simp [scan, bind, pure]
  have final := loop_one_update scan _ _ first last
  simp only [final, Id.run, bind, pure]

private theorem sifa4_empty (tags : Fin 6 → BorTag) (capacity : UInt64) :
    let tree := tree4 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
    source_sifa_update tree ⟨2⟩ .Read = (tree, .ok ()) := by
  let tree := tree4 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
  change source_sifa_update tree ⟨2⟩ .Read = (tree, .ok ())
  unfold_sifa
  simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte, ForIn.forIn]
  name_range_scan
  have first : scan () (none, tree, some (⟨2⟩ : UniIndex), 0, true) =
      .yield (none, tree, some (⟨2⟩ : UniIndex), 0, false) := by
    by_cases empty : capacity = 0 <;>
      simp [scan, tree, tree4, stageNode, rootLocation, empty, UniValMap.get,
        UniValMap.insert, UniValMap.extendTo, UniValMap.size, UniIndex.toNat,
        DedupRangeMap.new, DedupRangeMap.iterAll, DedupRangeMap.modifyAll, Size.ofBytes,
        IdempotentForeignAccess.ensureNoStrongerThan, IdempotentForeignAccess.rank, Id.run, bind, pure]
  have last : scan () (none, tree, some (⟨2⟩ : UniIndex), 0, false) =
      .done (none, tree, some (⟨2⟩ : UniIndex), 0, false) := by
    simp [scan, bind, pure]
  have final := loop_one_update scan _ _ first last
  simp only [final, Id.run, bind, pure]

theorem new_shared2_zero (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset : UInt64) :
    (tree2 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)).newChild
      (Size.ofBytes offset) (.concrete (tags 1)) (tags 2)
      (DedupRangeMap.new Size.ZERO frozenRead) .Frozen false =
      ⟨tree3 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation), .ok ()⟩ := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  have inserted : (tree2 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)).tagMapping.insert (tags 2) =
      .Inserted (tree3 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)).tagMapping ⟨2⟩ := by
    simp [tree2, tree3, canonicalChildTree, UniKeyMap.insert, UniKeyMap.get,
      UniIndex.ofNat?, eqTags, ← Array.find?_toList]
  unfold BorrowTree.newChild
  rw [inserted]
  simp only [Size.ZERO, ← Array.forIn_toList, tree2, tree3, canonicalChildTree, stageNode] at *
  simp_new_source
  have final := sifa3_empty tags capacity
  simpa only [DedupRangeMap.new, Size.ofBytes, beq_iff_eq] using
    (And.intro (congrArg Prod.fst final) (congrArg Prod.snd final))

#print axioms new_shared2_zero
theorem new_shared_entry3_zero (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset : UInt64) :
    (tree3 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)).newChild
      (Size.ofBytes offset) (.concrete (tags 2)) (tags 3)
      (DedupRangeMap.new Size.ZERO frozenRead) .Frozen true =
      ⟨tree4 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation), .ok ()⟩ := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  have inserted : (tree3 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)).tagMapping.insert (tags 3) =
      .Inserted (tree4 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)).tagMapping ⟨3⟩ := by
    simp [tree3, tree4, canonicalChildTree, UniKeyMap.insert, UniKeyMap.get,
      UniIndex.ofNat?, eqTags, ← Array.find?_toList]
  unfold BorrowTree.newChild
  rw [inserted]
  simp only [Size.ZERO, ← Array.forIn_toList, tree3, tree4, canonicalChildTree, stageNode] at *
  simp_new_source
  have final := sifa4_empty tags capacity
  simpa only [DedupRangeMap.new, Size.ofBytes, beq_iff_eq] using
    (And.intro (congrArg Prod.fst final) (congrArg Prod.snd final))

#print axioms new_shared_entry3_zero
theorem access_zero (tree : BorrowTree) (tag : BorTag) (index : UniIndex)
    (offset : Size) (kind : AccessKind) (protections : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (lookup : tree.indexOfTag tag = some index) :
    let result := tree.performBorrowAccessRange (.concrete tag) offset Size.ZERO kind protections mode
    result.status = .Completed ∧ result.tree = tree := by
  dsimp only
  unfold BorrowTree.performBorrowAccessRange
  dsimp only
  rw [lookup]
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  rw [RangeMapProof.iter_mut_empty_exact]
  simp [Id.run, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

private theorem release_root_only (tree : BorrowTree) (tag : BorTag) (index : UniIndex)
    (capacity : UInt64) (protections : ProtectedTags)
    (locations : tree.locations = DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
    (lookup : tree.indexOfTag tag = some index) (unmaterialized : rootLocation.perms.get index = none)
    (exposure : tree.updateExposureForProtectorRelease tag = ⟨tree, .ok ()⟩) :
    tree.releaseProtector tag protections = ⟨tree, .Released⟩ := by
  unfold BorrowTree.releaseProtector
  dsimp only
  rw [lookup]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  by_cases empty : capacity = 0
  all_goals
    simp only [locations, DedupRangeMap.new, Size.ofBytes, beq_iff_eq, empty, ↓reduceIte]
    simp [unmaterialized, exposure, locations, DedupRangeMap.new, Size.ofBytes, empty,
      Id.run, bind, pure, List.range'_succ, List.range'_zero]
    try simp_release_set

theorem len_release_zero (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity : UInt64) (protections : ProtectedTags) :
    let tree := tree4 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
    tree.releaseProtector (tags 3) protections = ⟨tree, .Released⟩ := by
  let tree := tree4 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  have lookup : tree.indexOfTag (tags 3) = some ⟨3⟩ := by
    simp [tree, tree4, canonicalChildTree, BorrowTree.indexOfTag, UniKeyMap.get, ← Array.find?_toList, eqTags]
  have exposure : tree.updateExposureForProtectorRelease (tags 3) = ⟨tree, .ok ()⟩ := by
    unfold BorrowTree.updateExposureForProtectorRelease
    dsimp only
    rw [lookup]
    simp [tree, BorrowTree.nodeAt, UniValMap.get, UniIndex.toNat, Id.run, pure]
  exact release_root_only tree (tags 3) ⟨3⟩ capacity protections rfl lookup (by rfl) exposure

#print axioms len_release_zero
theorem outer4_release_zero (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity : UInt64) (protections : ProtectedTags) :
    let tree := tree4 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
    tree.releaseProtector (tags 1) protections = ⟨tree, .Released⟩ := by
  let tree := tree4 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  have lookup : tree.indexOfTag (tags 1) = some ⟨1⟩ := by
    simp [tree, tree4, canonicalChildTree, BorrowTree.indexOfTag, UniKeyMap.get, ← Array.find?_toList, eqTags]
  have exposure : tree.updateExposureForProtectorRelease (tags 1) = ⟨tree, .ok ()⟩ := by
    unfold BorrowTree.updateExposureForProtectorRelease
    dsimp only
    rw [lookup]
    simp [tree, BorrowTree.nodeAt, UniValMap.get, UniIndex.toNat, Id.run, pure]
  exact release_root_only tree (tags 1) ⟨1⟩ capacity protections rfl lookup (by rfl) exposure

#print axioms outer4_release_zero
theorem outer2_release_zero (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity : UInt64) (protections : ProtectedTags) :
    let tree := tree2 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
    tree.releaseProtector (tags 1) protections = ⟨tree, .Released⟩ := by
  let tree := tree2 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  have lookup : tree.indexOfTag (tags 1) = some ⟨1⟩ := by
    simp [tree, tree2, canonicalChildTree, BorrowTree.indexOfTag, UniKeyMap.get, ← Array.find?_toList, eqTags]
  have exposure : tree.updateExposureForProtectorRelease (tags 1) = ⟨tree, .ok ()⟩ := by
    unfold BorrowTree.updateExposureForProtectorRelease
    dsimp only
    rw [lookup]
    simp [tree, BorrowTree.nodeAt, UniValMap.get, UniIndex.toNat, Id.run, pure]
  exact release_root_only tree (tags 1) ⟨1⟩ capacity protections rfl lookup (by rfl) exposure

#print axioms outer2_release_zero
theorem parent2_zero (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset : UInt64) (protections : ProtectedTags) :
    let tree := tree2 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
    let result := tree.performBorrowAccessRange (.concrete (tags 1)) (Size.ofBytes offset) Size.ZERO
      .Read protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = tree := by
  let tree := tree2 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  have lookup : tree.indexOfTag (tags 1) = some ⟨1⟩ := by
    simp [tree, tree2, canonicalChildTree, BorrowTree.indexOfTag, UniKeyMap.get, ← Array.find?_toList, eqTags]
  exact access_zero tree (tags 1) ⟨1⟩ (Size.ofBytes offset) .Read protections .VisitChildrenOfAccessed lookup

#print axioms parent2_zero
theorem parent3_zero (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset : UInt64) (protections : ProtectedTags) :
    let tree := tree3 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
    let result := tree.performBorrowAccessRange (.concrete (tags 2)) (Size.ofBytes offset) Size.ZERO
      .Read protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = tree := by
  let tree := tree3 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  have lookup : tree.indexOfTag (tags 2) = some ⟨2⟩ := by
    simp [tree, tree3, canonicalChildTree, BorrowTree.indexOfTag, UniKeyMap.get, ← Array.find?_toList, eqTags]
  exact access_zero tree (tags 2) ⟨2⟩ (Size.ofBytes offset) .Read protections .VisitChildrenOfAccessed lookup

#print axioms parent3_zero
structure Result where
  tree : BorrowTree
  accesses : Array BorrowTree.BorrowTreeAccessStatus
  insertions : Array (Except BorrowTree.ChildInsertError Unit)
  releases : Array BorrowTree.ProtectorReleaseStatus
  deriving DecidableEq, Repr

/-- Exact buffer-tree operations on the empty len-helper path. Global table
registration/removal belongs to the caller, and these tables may contain any
unrelated protected tags. -/
def prepare_zero (tags : Fin 6 → BorTag) (capacity offset : UInt64)
    (sharedProtected lenProtected lenReturnProtected outerProtected : ProtectedTags) : Result :=
  let initial := tree2 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
  let sharedRead := initial.performBorrowAccessRange (.concrete (tags 1)) (Size.ofBytes offset) Size.ZERO
    .Read sharedProtected .VisitChildrenOfAccessed
  let shared := sharedRead.tree.newChild (Size.ofBytes offset) (.concrete (tags 1)) (tags 2)
    (DedupRangeMap.new Size.ZERO frozenRead) .Frozen false
  let lenRead := shared.tree.performBorrowAccessRange (.concrete (tags 2)) (Size.ofBytes offset) Size.ZERO
    .Read lenProtected .VisitChildrenOfAccessed
  let lenChild := lenRead.tree.newChild (Size.ofBytes offset) (.concrete (tags 2)) (tags 3)
    (DedupRangeMap.new Size.ZERO frozenRead) .Frozen true
  let lenReturn := lenChild.tree.releaseProtector (tags 3) lenReturnProtected
  let outerReturn := lenReturn.tree.releaseProtector (tags 1) outerProtected
  { tree := outerReturn.tree
    accesses := #[sharedRead.status, lenRead.status]
    insertions := #[shared.outcome, lenChild.outcome]
    releases := #[lenReturn.status, outerReturn.status] }

theorem prepare_zero_exact (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (capacity offset : UInt64) (sharedProtected lenProtected lenReturnProtected outerProtected : ProtectedTags) :
    prepare_zero tags capacity offset sharedProtected lenProtected lenReturnProtected outerProtected =
      { tree := tree4 tags (DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
        accesses := #[.Completed, .Completed]
        insertions := #[.ok (), .ok ()]
        releases := #[.Released, .Released] } := by
  have read2 := parent2_zero tags distinct capacity offset sharedProtected
  have child2 := new_shared2_zero tags distinct capacity offset
  have read3 := parent3_zero tags distinct capacity offset lenProtected
  have child3 := new_shared_entry3_zero tags distinct capacity offset
  have release3 := len_release_zero tags distinct capacity lenReturnProtected
  have release1 := outer4_release_zero tags distinct capacity outerProtected
  dsimp only at read2 read3 child2 child3 release3 release1
  simp only [prepare_zero, read2.2, child2, read3.2, child3, release3, release1, read2.1, read3.1]

#print axioms prepare_zero_exact
#print axioms access_zero
end DuplicatePrefix.EmptyBorrowHelpers

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.EmptyBorrowHelpers.new_shared2_zero,
      ``DuplicatePrefix.EmptyBorrowHelpers.new_shared_entry3_zero,
      ``DuplicatePrefix.EmptyBorrowHelpers.parent2_zero, ``DuplicatePrefix.EmptyBorrowHelpers.parent3_zero,
      ``DuplicatePrefix.EmptyBorrowHelpers.len_release_zero,
      ``DuplicatePrefix.EmptyBorrowHelpers.outer2_release_zero, ``DuplicatePrefix.EmptyBorrowHelpers.outer4_release_zero,
      ``DuplicatePrefix.EmptyBorrowHelpers.prepare_zero_exact] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
