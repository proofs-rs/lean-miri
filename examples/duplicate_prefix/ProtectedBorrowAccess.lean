import duplicate_prefix.NestedBorrowAccess
import duplicate_prefix.MixedRelease

/-! Access contracts depend only on protection of nodes in the allocation's
borrow tree; protectors for unrelated allocations remain unrestricted. -/
namespace DuplicatePrefix.ProtectedBorrowAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open BorrowRangeAccess NestedBorrowAccess MixedRangeMap
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

/-- The optional helper protector may remain active. Other protected tags are
unrestricted, including tags belonging to return and caller-location allocations. -/
def SixMask (tags : Fin 6 → BorTag) (protections : ProtectedTags) (helper : Bool) : Prop :=
  ∀ i : Fin 6, protections.contains (tags i) = (i == 1 || helper && i == 5)

theorem projection2 (root child : BorTag) (locations : DedupRangeMap LocationTree)
    (written : Bool) (protections : ProtectedTags)
    (rootFree : protections.contains root = false) (childHeld : protections.contains child = true) :
    source_normal_projection (canonicalChildTree root child locations) (childLocation written) protections =
      childNormal written := by
  simp_tree_helpers
  simp [canonicalChildTree, childLocation, childNormal, rootFree, childHeld,
    UniValMap.get, UniValMap.entries, UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero, Id.run]

theorem projection6 (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree)
    (written helper : Bool) (protections : ProtectedTags) (mask : SixMask tags protections helper) :
    source_normal_projection (nestedTree tags locations) (nestedLocation written) protections =
      nestedNormalWithHelper written helper := by
  unfold SixMask at mask
  cases helper <;> simp_tree_helpers <;>
    simp [nestedTree, nestedLocation, nestedNormal, nestedNormalWithHelper, mask,
      UniValMap.get, UniValMap.entries, UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
      bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.range'_succ, List.range'_zero, Id.run]

abbrev access2 (root child : BorTag) (locations : DedupRangeMap LocationTree)
    (written : Bool) (kind : AccessKind) (mode : Tree.ChildrenVisitMode)
    (protections : ProtectedTags) (range : ByteRange) :=
  source_tree_access_at (canonicalChildTree root child locations) (childLocation written)
    (some ⟨1⟩) kind protections mode range

abbrev access6 (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree)
    (written : Bool) (kind : AccessKind) (mode : Tree.ChildrenVisitMode)
    (protections : ProtectedTags) (range : ByteRange) :=
  source_tree_access_at (nestedTree tags locations) (nestedLocation written)
    (some ⟨5⟩) kind protections mode range

theorem access2_local (rootTag childTag : BorTag) (locations : DedupRangeMap LocationTree)
    (written : Bool) (kind : AccessKind) (mode : Tree.ChildrenVisitMode) (range : ByteRange)
    (distinct : rootTag ≠ childTag) (protections : ProtectedTags)
    (rootFree : protections.contains rootTag = false) (childHeld : protections.contains childTag = true) :
    source_access_location (access2 rootTag childTag locations written kind mode protections range) =
      childLocation (written || kind == .Write) ∧
    source_access_status (access2 rootTag childTag locations written kind mode protections range) = none := by
  unfold access2
  simp_tree_helpers
  simp only [BorrowTree.performNormalAccessAt,
    projection2 rootTag childTag locations written protections rootFree childHeld, UniIndex.toNat, child_normal_access]
  simp [canonicalChildTree, childLocation, childNormal, childProtected, canonical_min_exposed,
    BorrowTree.nodeAt, UniValMap.insert, UniValMap.extendTo, UniValMap.get, UniValMap.entries,
    UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    rootFree, childHeld, distinct, Ne.symm distinct,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp_tree_helpers
  try simp only [child_normal_access, canonical_min_exposed]
  simp [Id.run, UniIndex.toNat, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
    BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero, canonical_min_exposed]

theorem access6_local (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) (written helperProtected : Bool)
    (protections : ProtectedTags) (mask : SixMask tags protections helperProtected) (kind : AccessKind) (mode : Tree.ChildrenVisitMode) (range : ByteRange) :
    source_access_location (access6 tags locations written kind mode protections range) =
      nestedLocation (written || kind == .Write) ∧
    source_access_status (access6 tags locations written kind mode protections range) = none := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  unfold access6
  simp_tree_helpers
  simp only [BorrowTree.performNormalAccessAt, projection6 tags locations written helperProtected protections mask,
    show (⟨5⟩ : UniIndex).toNat = 5 from rfl, nested_normal_with_helper_access, nested_min_exposed]
  simp [nestedTree, nestedLocation, nestedNormalWithHelper, nestedNormal, nestedVisits, nestedProtectedWithHelper, nestedProtected, childProtected,
    BorrowTree.nodeAt, UniValMap.get, UniValMap.entries,
    UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    eqTags,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]
  simp_tree_helpers
  try simp only [nested_normal_with_helper_access, nested_min_exposed]
  simp [nested_min_exposed, Id.run, UniIndex.toNat, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
    BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]
  all_goals cases written <;> cases helperProtected <;> cases kind <;> cases mode <;>
    simp [nestedVisits, nestedNormalWithHelper, nestedNormal, nestedLocation, reserved, frozenBranch, Id.run,
      UniIndex.toNat, UniIndex.ofNat?, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
      BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.range'_succ, List.range'_zero]

private theorem range_prepared (tree : BorrowTree) (tag : BorTag) (source : UniIndex)
    (offset len : Size) (kind : AccessKind) (protections : ProtectedTags) (mode : Tree.ChildrenVisitMode)
    (prepared output : DedupRangeMap LocationTree) (position : Nat) (segment : RangeMapSegment LocationTree)
    (replacement : LocationTree)
    (lookup : tree.indexOfTag tag = some source)
    (iterator : tree.locations.iterMut offset len = ⟨prepared, #[position], #[segment], .ok ()⟩)
    (localFact : source_access_location (source_tree_access_at tree segment.data (some source) kind protections mode segment.range) = replacement ∧
      source_access_status (source_tree_access_at tree segment.data (some source) kind protections mode segment.range) = none)
    (mutation : prepared.setAtPos position replacement = ⟨output, .ok ()⟩) :
    let result := tree.performBorrowAccessRange (.concrete tag) offset len kind protections mode
    result.status = .Completed ∧ result.tree = {tree with locations := output} := by
  dsimp only
  unfold BorrowTree.performBorrowAccessRange
  dsimp only
  rw [lookup]
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  rw [iterator]
  simp [localFact.1, localFact.2, mutation, Id.run, bind, pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem read2 (root child : BorTag) (protections : ProtectedTags)
    (rootFree : protections.contains root = false) (childHeld : protections.contains child = true)
    (capacity offset len finish : UInt64) (distinct : root ≠ child)
    (positive : (0 : UInt64) < len) (interior : offset.toNat + len.toNat < finish.toNat) :
    let initial := canonicalChildTree root child (partitionWithInside capacity offset finish rootLocation (childLocation false))
    let result := initial.performBorrowAccessRange (.concrete child) (Size.ofBytes offset) (Size.ofBytes len)
      .Read protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = canonicalChildTree root child (splitInside capacity offset finish (offset + len) rootLocation (childLocation false)) := by
  have callback := access2_local root child (partitionWithInside capacity offset finish rootLocation (childLocation false)) false .Read .VisitChildrenOfAccessed ⟨offset, offset + len⟩ distinct protections rootFree childHeld
  have readNotWrite : (AccessKind.Read == AccessKind.Write) = false := by decide
  simp only [readNotWrite, Bool.false_or] at callback
  have fact := range_prepared (canonicalChildTree root child (partitionWithInside capacity offset finish rootLocation (childLocation false))) child ⟨1⟩
    (Size.ofBytes offset) (Size.ofBytes len) .Read protections .VisitChildrenOfAccessed
    (splitInside capacity offset finish (offset + len) rootLocation (childLocation false)) (splitInside capacity offset finish (offset + len) rootLocation (childLocation false)) (RangeMapNonempty.intervalPosition offset)
    ⟨⟨offset, offset + len⟩, childLocation false⟩ (childLocation false)
    (canonical_child_index root child _ distinct)
    (iterMut_initial_prefix capacity offset len finish rootLocation (childLocation false) positive interior)
    callback (split_set_same capacity offset finish (offset + len) rootLocation (childLocation false))
  simpa [canonicalChildTree] using fact

theorem write2 (root child : BorTag) (protections : ProtectedTags)
    (rootFree : protections.contains root = false) (childHeld : protections.contains child = true)
    (capacity offset finish first len : UInt64) (distinct : root ≠ child)
    (positive : (0 : UInt64) < len) (afterStart : offset < first)
    (bounds : first.toNat + len.toNat ≤ finish.toNat) :
    let initial := canonicalChildTree root child (splitInside capacity offset finish first rootLocation (childLocation false))
    let result := initial.performBorrowAccessRange (.concrete child) (Size.ofBytes first) (Size.ofBytes len)
      .Write protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = canonicalChildTree root child (doubleSplit capacity offset finish first (first + len) rootLocation (childLocation false) (childLocation true) (childLocation false)) := by
  have callback := access2_local root child (splitInside capacity offset finish first rootLocation (childLocation false)) false .Write .VisitChildrenOfAccessed ⟨first, first + len⟩ distinct protections rootFree childHeld
  have writeIsWrite : (AccessKind.Write == AccessKind.Write) = true := by decide
  simp only [writeIsWrite, Bool.false_or] at callback
  have fact := range_prepared (canonicalChildTree root child (splitInside capacity offset finish first rootLocation (childLocation false))) child ⟨1⟩
    (Size.ofBytes first) (Size.ofBytes len) .Write protections .VisitChildrenOfAccessed
    (doubleSplit capacity offset finish first (first + len) rootLocation (childLocation false) (childLocation false) (childLocation false)) (doubleSplit capacity offset finish first (first + len) rootLocation (childLocation false) (childLocation true) (childLocation false)) (secondPosition offset)
    ⟨⟨first, first + len⟩, childLocation false⟩ (childLocation true)
    (canonical_child_index root child _ distinct)
    (iterMut_second_prefix capacity offset finish first len rootLocation (childLocation false) positive afterStart bounds)
    callback (double_set_middle capacity offset finish first (first + len) rootLocation (childLocation false) (childLocation true))
  simpa [canonicalChildTree] using fact

theorem canonical_slice_copy_borrow2 (root child : BorTag) (protections : ProtectedTags)
    (rootFree : protections.contains root = false) (childHeld : protections.contains child = true)
    (capacity offset sliceLen n : UInt64) (distinct : root ≠ child)
    (positive : (0 : UInt64) < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ capacity.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat) :
    let initial := canonicalChildTree root child
      (partitionWithInside capacity offset (offset + sliceLen) rootLocation (childLocation false))
    let read := initial.performBorrowAccessRange (.concrete child)
      (Size.ofBytes offset) (Size.ofBytes n) .Read (protections) .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete child)
      (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write (protections) .VisitChildrenOfAccessed
    read.status = .Completed ∧ write.status = .Completed ∧
      write.tree = canonicalChildTree root child
        (doubleSplit capacity offset (offset + sliceLen) (offset + n) ((offset + n) + n)
          rootLocation (childLocation false) (childLocation true) (childLocation false)) := by
  have fits : offset.toNat + sliceLen.toNat < 2^64 := by have limit := capacity.toNat_lt; omega
  have endNat : (offset + sliceLen).toNat = offset.toNat + sliceLen.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have prefixFits : offset.toNat + n.toNat < 2^64 := by omega
  have middleNat : (offset + n).toNat = offset.toNat + n.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt prefixFits]
  have posNat : 0 < n.toNat := by simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] using positive
  have prefixInterior : offset.toNat + n.toNat < (offset + sliceLen).toNat := by omega
  have afterStart : offset < offset + n := by simp only [UInt64.lt_iff_toNat_lt, middleNat]; omega
  have suffixBounds : (offset + n).toNat + n.toNat ≤ (offset + sliceLen).toNat := by omega
  have readFact := read2 root child protections rootFree childHeld capacity offset n (offset + sliceLen)
    distinct positive prefixInterior
  have writeFact := write2 root child protections rootFree childHeld capacity offset (offset + sliceLen) (offset + n) n
    distinct positive afterStart suffixBounds
  dsimp only at readFact writeFact ⊢
  exact ⟨readFact.1, by rw [readFact.2]; exact writeFact.1, by rw [readFact.2]; exact writeFact.2⟩


#print axioms canonical_slice_copy_borrow2
theorem read6 (tags : Fin 6 → BorTag) (protections : ProtectedTags) (mask : SixMask tags protections false)
    (capacity offset len finish : UInt64) (distinct : Function.Injective tags)
    (positive : (0 : UInt64) < len) (interior : offset.toNat + len.toNat < finish.toNat) :
    let initial := nestedTree tags (partitionWithInside capacity offset finish rootLocation (nestedLocation false))
    let result := initial.performBorrowAccessRange (.concrete (tags 5)) (Size.ofBytes offset) (Size.ofBytes len)
      .Read protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = nestedTree tags (splitInside capacity offset finish (offset + len) rootLocation (nestedLocation false)) := by
  have callback := access6_local tags distinct (partitionWithInside capacity offset finish rootLocation (nestedLocation false)) false false protections mask .Read .VisitChildrenOfAccessed ⟨offset, offset + len⟩
  have readNotWrite : (AccessKind.Read == AccessKind.Write) = false := by decide
  simp only [readNotWrite, Bool.false_or] at callback
  have fact := range_prepared (nestedTree tags (partitionWithInside capacity offset finish rootLocation (nestedLocation false))) (tags 5) ⟨5⟩
    (Size.ofBytes offset) (Size.ofBytes len) .Read protections .VisitChildrenOfAccessed
    (splitInside capacity offset finish (offset + len) rootLocation (nestedLocation false)) (splitInside capacity offset finish (offset + len) rootLocation (nestedLocation false)) (RangeMapNonempty.intervalPosition offset)
    ⟨⟨offset, offset + len⟩, nestedLocation false⟩ (nestedLocation false)
    (nested_index tags distinct _)
    (iterMut_initial_prefix capacity offset len finish rootLocation (nestedLocation false) positive interior)
    callback (split_set_same capacity offset finish (offset + len) rootLocation (nestedLocation false))
  simpa [nestedTree] using fact

theorem write6 (tags : Fin 6 → BorTag) (protections : ProtectedTags) (mask : SixMask tags protections false)
    (capacity offset finish first len : UInt64) (distinct : Function.Injective tags)
    (positive : (0 : UInt64) < len) (afterStart : offset < first)
    (bounds : first.toNat + len.toNat ≤ finish.toNat) :
    let initial := nestedTree tags (splitInside capacity offset finish first rootLocation (nestedLocation false))
    let result := initial.performBorrowAccessRange (.concrete (tags 5)) (Size.ofBytes first) (Size.ofBytes len)
      .Write protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = nestedTree tags (doubleSplit capacity offset finish first (first + len) rootLocation (nestedLocation false) (nestedLocation true) (nestedLocation false)) := by
  have callback := access6_local tags distinct (splitInside capacity offset finish first rootLocation (nestedLocation false)) false false protections mask .Write .VisitChildrenOfAccessed ⟨first, first + len⟩
  have writeIsWrite : (AccessKind.Write == AccessKind.Write) = true := by decide
  simp only [writeIsWrite, Bool.false_or] at callback
  have fact := range_prepared (nestedTree tags (splitInside capacity offset finish first rootLocation (nestedLocation false))) (tags 5) ⟨5⟩
    (Size.ofBytes first) (Size.ofBytes len) .Write protections .VisitChildrenOfAccessed
    (doubleSplit capacity offset finish first (first + len) rootLocation (nestedLocation false) (nestedLocation false) (nestedLocation false)) (doubleSplit capacity offset finish first (first + len) rootLocation (nestedLocation false) (nestedLocation true) (nestedLocation false)) (secondPosition offset)
    ⟨⟨first, first + len⟩, nestedLocation false⟩ (nestedLocation true)
    (nested_index tags distinct _)
    (iterMut_second_prefix capacity offset finish first len rootLocation (nestedLocation false) positive afterStart bounds)
    callback (double_set_middle capacity offset finish first (first + len) rootLocation (nestedLocation false) (nestedLocation true))
  simpa [nestedTree] using fact

theorem canonical_slice_copy_borrow6 (tags : Fin 6 → BorTag) (protections : ProtectedTags) (mask : SixMask tags protections false)
    (capacity offset sliceLen n : UInt64) (distinct : Function.Injective tags)
    (positive : (0 : UInt64) < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ capacity.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat) :
    let initial := nestedTree tags
      (partitionWithInside capacity offset (offset + sliceLen) rootLocation (nestedLocation false))
    let read := initial.performBorrowAccessRange (.concrete (tags 5))
      (Size.ofBytes offset) (Size.ofBytes n) .Read (protections) .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete (tags 5))
      (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write (protections) .VisitChildrenOfAccessed
    read.status = .Completed ∧ write.status = .Completed ∧
      write.tree = nestedTree tags
        (doubleSplit capacity offset (offset + sliceLen) (offset + n) ((offset + n) + n)
          rootLocation (nestedLocation false) (nestedLocation true) (nestedLocation false)) := by
  have fits : offset.toNat + sliceLen.toNat < 2^64 := by have limit := capacity.toNat_lt; omega
  have endNat : (offset + sliceLen).toNat = offset.toNat + sliceLen.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have prefixFits : offset.toNat + n.toNat < 2^64 := by omega
  have middleNat : (offset + n).toNat = offset.toNat + n.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt prefixFits]
  have posNat : 0 < n.toNat := by simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] using positive
  have prefixInterior : offset.toNat + n.toNat < (offset + sliceLen).toNat := by omega
  have afterStart : offset < offset + n := by simp only [UInt64.lt_iff_toNat_lt, middleNat]; omega
  have suffixBounds : (offset + n).toNat + n.toNat ≤ (offset + sliceLen).toNat := by omega
  have readFact := read6 tags protections mask capacity offset n (offset + sliceLen)
    distinct positive prefixInterior
  have writeFact := write6 tags protections mask capacity offset (offset + sliceLen) (offset + n) n
    distinct positive afterStart suffixBounds
  dsimp only at readFact writeFact ⊢
  exact ⟨readFact.1, by rw [readFact.2]; exact writeFact.1, by rw [readFact.2]; exact writeFact.2⟩



#print axioms canonical_slice_copy_borrow6
#print axioms access2_local
#print axioms access6_local
end DuplicatePrefix.ProtectedBorrowAccess

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ProtectedBorrowAccess.canonical_slice_copy_borrow2,
      ``DuplicatePrefix.ProtectedBorrowAccess.canonical_slice_copy_borrow6,
      ``DuplicatePrefix.ProtectedBorrowAccess.access2_local, ``DuplicatePrefix.ProtectedBorrowAccess.access6_local] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
