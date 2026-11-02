import duplicate_prefix.GeneralBorrowFreshReuseState
namespace DuplicatePrefix.GeneralBorrowFreshReuseProtection
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowFreshNode
open DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

private theorem converted_nat (position : Nat) (index : UniIndex)
    (converted : UniIndex.ofNat? position = some index) : index.toNat = position := by
  unfold UniIndex.ofNat? at converted
  split at converted
  next bounded =>
    cases converted
    simp only [UniIndex.toNat,UInt32.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  next => contradiction

/-- The actual optional-slot enumeration contains precisely the successful lookups. -/
theorem entries_get {α : Type} (nodes : UniValMap α) (query : UniIndex) (value : α) :
    (query,value) ∈ nodes.entries.toList ↔ nodes.get query = some value := by
  rw [GeneralBorrowFreshEntries.entries_formula]
  simp only [List.toList_toArray,List.mem_filterMap]
  constructor
  · rintro ⟨position,member,found⟩
    unfold GeneralBorrowFreshEntries.slot at found
    cases converted : UniIndex.ofNat? position with
    | none => simp [converted] at found
    | some index =>
      have equal := converted_nat position index converted
      cases stored : nodes.data[position]? with
      | none => simp [converted,stored] at found
      | some cell =>
        cases cell with
        | none => simp [converted,stored] at found
        | some actual =>
          simp only [converted,stored,Option.some.injEq,Prod.mk.injEq] at found
          rcases found with ⟨same,exactValue⟩
          subst index
          subst actual
          simp only [UniValMap.get,equal,stored]
  · intro lookup
    have stored : nodes.data[query.toNat]? = some (some value) := by
      unfold UniValMap.get at lookup
      cases entry : nodes.data[query.toNat]? with
      | none => simp [entry] at lookup
      | some cell => simpa only [entry] using congrArg some lookup
    have valid : query.toNat < nodes.data.size := by
      by_cases bound : query.toNat < nodes.data.size
      · exact bound
      · simp [Array.getElem?_eq_none (xs := nodes.data) (i := query.toNat) (by omega)] at stored
    refine ⟨query.toNat,?_,?_⟩
    · simp only [List.mem_range'_1]
      omega
    · simp only [GeneralBorrowFreshEntries.slot,index_self query,stored]

/-- Protection membership is determined by the actual node lookup and its tag;
location permissions do not enter this test. -/
theorem protected_iff (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (query : UniIndex) :
    query.toNat ∈ (source_normal_projection tree location protections).protectedNodes ↔
      ∃ node, tree.nodeAt query = some node ∧ protections.contains node.tag = true := by
  unfold_general_projection
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨⟨index,node⟩,member,found⟩
    have choice : index.toNat = query.toNat ∧ protections.contains node.tag = true := by
      split at found
      next held => exact ⟨Option.some.inj found,held⟩
      next => contradiction
    have same : index = query := by
      cases index with | mk left =>
        cases query with | mk right =>
          congr 1
          exact UInt32.toNat_inj.mp choice.1
    subst index
    exact ⟨node,(entries_get tree.nodes query node).mp member,choice.2⟩
  · rintro ⟨node,lookup,held⟩
    exact ⟨(query,node),(entries_get tree.nodes query node).mpr lookup,by simp [held]⟩

/-- Both concrete node insertions preserve every old tag away from the reused
slot, even when the queried node is the parent whose children were updated. -/
theorem tags_other (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (different : query ≠ index) :
    ((GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodeAt query).map TreeNode.tag =
      (tree.nodeAt query).map TreeNode.tag := by
  have old := (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode
    (GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index parent parentNode vacant parentPresent)).trans parentPresent
  change tree.nodes.get parent = some parentNode at parentPresent
  dsimp only [GeneralBorrowFreshGraph.attached,attachedNodes,BorrowTree.nodeAt]
  by_cases same : query = parent
  · subst query
    rw [insert_existing_get_same (tree.nodes.insert index newNode) parent parentNode _ old,parentPresent]
    rfl
  · rw [insert_existing_get_other (tree.nodes.insert index newNode) parent query parentNode _ old same,
      GeneralBorrowFreshLocation.get_other tree.nodes index query newNode different]

/-- Reusing a vacant node-table slot leaves all nonreused protection bits
unchanged. Arbitrary old protection histories are allowed. -/
theorem protection_old (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (query : UniIndex) (different : query ≠ index) :
    (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) newLocation protections).protectedNodes.contains query.toNat =
      (source_normal_projection tree oldLocation protections).protectedNodes.contains query.toNat := by
  have tags := tags_other tree index parent query parentNode newNode vacant parentPresent different
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem,protected_iff]
  cases before : tree.nodeAt query with
  | none =>
    cases after : (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodeAt query with
    | none => simp [before,after]
    | some node => simp [before,after] at tags
  | some oldNode =>
    cases after : (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodeAt query with
    | none => simp [before,after] at tags
    | some node =>
      have tagEq : node.tag = oldNode.tag := by simpa only [before,after,Option.map_some,Option.some.injEq] using tags
      simp [before,after,tagEq]
/-- Natural-index form used while traversing the projected normal forest. -/
theorem protection_position (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (fits : tree.nodes.data.size ≤ 4294967296) (position : Nat)
    (valid : position < tree.nodes.data.size) (different : position ≠ index.toNat) :
    (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) newLocation protections).protectedNodes.contains position =
      (source_normal_projection tree oldLocation protections).protectedNodes.contains position := by
  obtain ⟨query,converted,equal⟩ := index_nat position (by omega)
  have queryDifferent : query ≠ index := by
    intro same
    exact different (equal.symm.trans (congrArg UniIndex.toNat same))
  simpa only [equal] using protection_old tree index parent parentNode newNode vacant parentPresent
    oldLocation newLocation protections query queryDifferent

/-- The reused child's protection bit is exactly its new tag's protection. -/
theorem protection_new (tree : BorrowTree) (index parent : UniIndex) (parentNode newNode : TreeNode)
    (vacant : tree.nodes.get index = none) (parentPresent : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode) location protections).protectedNodes.contains index.toNat =
      protections.contains newNode.tag := by
  have different := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index parent parentNode vacant parentPresent
  have parentOld := (GeneralBorrowFreshLocation.get_other tree.nodes index parent newNode different).trans parentPresent
  have child : (GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodeAt index = some newNode := by
    dsimp only [GeneralBorrowFreshGraph.attached,attachedNodes,BorrowTree.nodeAt]
    rw [insert_existing_get_other (tree.nodes.insert index newNode) parent index parentNode _ parentOld (Ne.symm different),
      GeneralBorrowFreshLocation.get_same]
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem,protected_iff,child,Option.some.injEq]
  simp

end DuplicatePrefix.GeneralBorrowFreshReuseProtection
