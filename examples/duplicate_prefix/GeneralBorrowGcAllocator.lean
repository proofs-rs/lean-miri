import duplicate_prefix.GeneralBorrowSparseRemoval
import duplicate_prefix.GeneralBorrowFreshStagePool
namespace DuplicatePrefix.GeneralBorrowGcAllocator
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshAllocatorInvariant DuplicatePrefix.GeneralBorrowFreshStagePool
open DuplicatePrefix.GeneralBorrowSparseRemoval
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- The source tag map removes all matching rows. Unique keys are therefore a
separate initial-history invariant, not a consequence of Pool or Accounting. -/
def KeyUnique (mapping : UniKeyMap BorTag) : Prop := (mapping.mapping.toList.map Prod.fst).Nodup

private theorem filter_key_length (keys : List BorTag) (tag : BorTag) (unique : keys.Nodup) (member : tag ∈ keys) :
    (keys.filter (fun key => key != tag)).length+1 = keys.length := by
  induction keys with
  | nil => simp at member
  | cons key rest ih =>
    have distinct := List.nodup_cons.mp unique
    by_cases same : key = tag
    · subst key
      have unchanged : rest.filter (fun key => key != tag) = rest := by
        apply List.filter_eq_self.mpr
        intro key member
        have different : key ≠ tag := by intro same;subst key;exact distinct.1 member
        simpa only [bne_iff_ne] using different
      simp only [List.filter_cons,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,unchanged,List.length_cons]
    · have tail : tag ∈ rest := by
        rcases List.mem_cons.mp member with equal | member
        · exact False.elim (same equal.symm)
        · exact member
      have count := ih distinct.2 tail
      simpa [same] using count

private theorem tag_member (mapping : UniKeyMap BorTag) (tag : BorTag) (index : UniIndex)
    (lookup : mapping.get tag = some index) : tag ∈ mapping.mapping.toList.map Prod.fst := by
  unfold UniKeyMap.get at lookup
  cases found : mapping.mapping.find? (fun row => row.1 == tag) with
  | none => simp [found] at lookup
  | some row =>
    have member := Array.mem_of_find?_eq_some found
    have predicate := Array.find?_some found
    have equal : row.1 = tag := by simpa only [beq_iff_eq] using predicate
    exact List.mem_map.mpr ⟨row,Array.mem_toList_iff.mpr member,equal⟩

theorem remove_mapping_size (mapping : UniKeyMap BorTag) (tag : BorTag) (index : UniIndex)
    (lookup : mapping.get tag = some index) (unique : KeyUnique mapping) :
    (mapping.remove tag).mapping.size+1 = mapping.mapping.size := by
  have count := filter_key_length (mapping.mapping.toList.map Prod.fst) tag unique (tag_member mapping tag index lookup)
  rw [List.filter_map] at count
  change (mapping.remove tag).mapping.toList.length+1 = mapping.mapping.toList.length
  simpa only [UniKeyMap.remove,lookup,Array.toList_filter,List.length_map,Function.comp_def] using count

theorem remove_unique (mapping : UniKeyMap BorTag) (tag : BorTag) (unique : KeyUnique mapping) : KeyUnique (mapping.remove tag) := by
  unfold UniKeyMap.remove
  split
  · exact unique
  · unfold KeyUnique
    simp only [Array.toList_filter]
    change ((mapping.mapping.toList.filter ((fun key : BorTag => key != tag) ∘ Prod.fst)).map Prod.fst).Nodup
    rw [←List.filter_map]
    exact unique.filter _

/-- Removing a present node adds a fresh vacant free slot. Existing free slots
remain bounded and vacant, and actual node capacity is unchanged. -/
theorem remove_pool (nodes : UniValMap TreeNode) (free : Array UniIndex)
    (pool : Pool nodes free) (index : UniIndex) (node : TreeNode) (present : nodes.get index = some node) :
    Pool (nodes.remove index) (free.push index) := by
  have valid := GeneralBorrowNodeUpdate.lookup_valid nodes index node present
  have absent : index ∉ free := by
    intro member
    have vacant := pool.vacant index member
    rw [present] at vacant
    cases vacant
  refine ⟨?_,?_,?_⟩
  · intro query member
    change query.toNat < (nodes.remove index).size
    rw [remove_size]
    rcases Array.mem_push.mp member with old | same
    · exact pool.bounded query old
    · subst query;exact valid
  · intro query member
    rcases Array.mem_push.mp member with old | same
    · have different : query ≠ index := by intro same;subst query;exact absent old
      rw [remove_get_other nodes index query different]
      exact pool.vacant query old
    · subst query;exact GeneralBorrowFreshDeassignment.get_removed nodes index
  · simp only [Array.toList_push]
    apply List.nodup_append.mpr
    refine ⟨pool.nodup,by simp,?_⟩
    intro query member last singleton
    have equal : last = index := by simpa only [List.mem_singleton] using singleton
    subst last
    intro same
    subst query
    exact absent (Array.mem_toList_iff.mp member)

/-- The exact production GC node-removal primitive preserves the allocator
invariants, given its node/tag-index correspondence and unique tag keys.
Eligibility for GC and preservation of that correspondence across a whole GC
walk remain separate obligations; operation success is derived here. -/
theorem remove_actual (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (lookup : tree.tagMapping.get node.tag = some index)
    (pool : Pool tree.nodes tree.tagMapping.deassigned) (accounting : Accounting tree) (unique : KeyUnique tree.tagMapping) :
    let result := source_remove_useless_node tree index
    result.2 = .ok () ∧ Pool result.1.nodes result.1.tagMapping.deassigned ∧ Accounting result.1 ∧ KeyUnique result.1.tagMapping := by
  have nextPool := remove_pool tree.nodes tree.tagMapping.deassigned pool index node present
  have count := remove_mapping_size tree.tagMapping node.tag index lookup unique
  have nextUnique := remove_unique tree.tagMapping node.tag unique
  unfold_source_remove_useless_node
  simp only [present,Id.run,pure]
  refine ⟨True.intro,?_,?_,nextUnique⟩
  · change Pool (tree.nodes.remove index) (tree.tagMapping.remove node.tag).deassigned
    simpa only [UniKeyMap.remove,lookup] using nextPool
  · change (tree.tagMapping.remove node.tag).mapping.size + (tree.tagMapping.remove node.tag).deassigned.size =
      (tree.nodes.remove index).size
    rw [remove_size]
    have freeSize : (tree.tagMapping.remove node.tag).deassigned.size = tree.tagMapping.deassigned.size+1 := by
      simp only [UniKeyMap.remove,lookup,Array.size_push]
    rw [freeSize]
    unfold Accounting at accounting
    omega

/-- Every live node's tag resolves to that same index in the actual tag map. -/
def NodeTags (tree : BorrowTree) : Prop :=
  ∀ index node, tree.nodes.get index = some node → tree.tagMapping.get node.tag = some index

theorem remove_lookup_other (mapping : UniKeyMap BorTag) (tag query : BorTag) (different : query ≠ tag) :
    (mapping.remove tag).get query = mapping.get query := by
  unfold UniKeyMap.remove
  split
  · rfl
  · unfold UniKeyMap.get
    rw [Array.find?_filter]
    have predicates : (fun row : BorTag × UniIndex => decide (row.1 != tag ∧ row.1 == query)) =
        (fun row => row.1 == query) := by
      funext row
      by_cases same : row.1 = query <;> simp [same,different]
    rw [predicates]

theorem removed_node_tags (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (coherent : NodeTags tree) :
    NodeTags {tree with nodes := tree.nodes.remove index,tagMapping := tree.tagMapping.remove node.tag} := by
  intro query next presentAfter
  change (tree.nodes.remove index).get query = some next at presentAfter
  have different : query ≠ index := by
    intro same
    subst query
    rw [GeneralBorrowFreshDeassignment.get_removed] at presentAfter
    cases presentAfter
  have presentBefore : tree.nodes.get query = some next := by
    rw [remove_get_other tree.nodes index query different] at presentAfter
    exact presentAfter
  have oldLookup := coherent query next presentBefore
  have removedLookup := coherent index node present
  have differentTag : next.tag ≠ node.tag := by
    intro same
    rw [same,removedLookup] at oldLookup
    exact different (Option.some.inj oldLookup.symm)
  change (tree.tagMapping.remove node.tag).get next.tag = some query
  rw [remove_lookup_other tree.tagMapping node.tag next.tag differentTag]
  exact oldLookup

set_option autoImplicit false in
/-- Sparse allocator history data only. This structure asserts neither GC
eligibility, graph well-formedness nor operation success. -/
structure Invariant (tree : BorrowTree) : Prop where
  pool : Pool tree.nodes tree.tagMapping.deassigned
  accounting : Accounting tree
  unique : KeyUnique tree.tagMapping
  nodeTags : NodeTags tree

/-- Both the successful primitive and MissingNode error retain the allocator
history invariant. No error outcome is being certified as safe execution. -/
theorem remove_step (tree : BorrowTree) (index : UniIndex) (invariant : Invariant tree) :
    Invariant (source_remove_useless_node tree index).1 := by
  cases present : tree.nodes.get index with
  | none =>
    unfold_source_remove_useless_node
    simpa only [present,Id.run,pure] using invariant
  | some node =>
    have kept := remove_actual tree index node present (invariant.nodeTags index node present)
      invariant.pool invariant.accounting invariant.unique
    have coherent := removed_node_tags tree index node present invariant.nodeTags
    refine ⟨kept.2.1,kept.2.2.1,kept.2.2.2,?_⟩
    unfold_source_remove_useless_node
    simpa only [present,Id.run,bind,pure,NodeTags] using coherent

/-- A finite composition of the exact removal primitive, stopping at its first
error just like a source GC removal loop. This is an induction cut, not a claim
that arbitrary removals are GC-eligible or that the full GC walker is verified. -/
def remove_list (tree : BorrowTree) (indices : List UniIndex) : BorrowTree × Except BorrowTree.TreeGcError Unit :=
  match indices with
  | [] => (tree,.ok ())
  | index :: rest =>
    let result := source_remove_useless_node tree index
    match result.2 with
    | .error _error => result
    | .ok () => remove_list result.1 rest

theorem remove_list_invariant (tree : BorrowTree) (indices : List UniIndex) (invariant : Invariant tree) :
    Invariant (remove_list tree indices).1 := by
  induction indices generalizing tree with
  | nil => exact invariant
  | cons index rest ih =>
    have kept := remove_step tree index invariant
    unfold remove_list
    dsimp only
    split
    · exact kept
    · exact ih _ kept


/-- Allocation creation establishes the complete allocator history invariant,
independently of allocation length and without a borrowing-history premise. -/
theorem initial (rootTag : BorTag) (size : Miri.ABI.Size) : Invariant (BorrowTree.new rootTag size) := by
  have capacity : (BorrowTree.new rootTag size).nodes.size = 1 := rfl
  have empty : (BorrowTree.new rootTag size).tagMapping.deassigned = #[] := rfl
  refine ⟨?_,?_,?_,?_⟩
  · rw [empty]
    exact ⟨by simp,by simp,by simp⟩
  · rfl
  · change ([rootTag] : List BorTag).Nodup
    simp
  · intro index node present
    have valid := GeneralBorrowNodeUpdate.lookup_valid (BorrowTree.new rootTag size).nodes index node present
    change index.toNat < (BorrowTree.new rootTag size).nodes.size at valid
    rw [capacity] at valid
    have equal : index = (⟨0⟩ : UniIndex) := GeneralBorrowNodeUpdate.index_injective index ⟨0⟩ (by change index.toNat = 0;omega)
    subst index
    rw [BorrowTree.new_root_node] at present
    cases present
    simp [BorrowTree.new,UniKeyMap.get]
    rfl

/-- The invariant holds after any finite actual-removal list starting at a new
allocation, including early errors. This certifies data preservation only. -/
theorem new_remove_list (rootTag : BorTag) (size : Miri.ABI.Size) (indices : List UniIndex) :
    Invariant (remove_list (BorrowTree.new rootTag size) indices).1 :=
  remove_list_invariant _ indices (initial rootTag size)


/-- The actual GC child/parent relinking insert changes node metadata while
preserving its tag. It preserves the allocator invariant without asserting
that the changed edges form a valid borrow graph. -/
theorem update_step (tree : BorrowTree) (index : UniIndex) (oldNode newNode : TreeNode)
    (present : tree.nodes.get index = some oldNode) (sameTag : newNode.tag = oldNode.tag)
    (invariant : Invariant tree) : Invariant {tree with nodes := tree.nodes.insert index newNode} := by
  refine ⟨GeneralBorrowFreshAllocatorInvariant.update_present tree.nodes tree.tagMapping.deassigned invariant.pool index oldNode newNode present,
    ?_,invariant.unique,?_⟩
  · unfold Accounting
    rw [GeneralBorrowNodeUpdate.insert_existing_size tree.nodes index oldNode newNode present]
    exact invariant.accounting
  · intro query node lookup
    change (tree.nodes.insert index newNode).get query = some node at lookup
    by_cases same : query = index
    · subst query
      rw [GeneralBorrowFreshLocation.get_same] at lookup
      cases lookup
      change tree.tagMapping.get newNode.tag = some index
      rw [sameTag]
      exact invariant.nodeTags index oldNode present
    · rw [GeneralBorrowFreshLocation.get_other tree.nodes index query newNode same] at lookup
      exact invariant.nodeTags query node lookup

/-- Fresh actual tag-map insertions append one unique key whether their chosen
node index is appended or reused. Free-pool behavior is handled separately. -/
theorem fresh_push_unique (mapping : UniKeyMap BorTag) (tag : BorTag) (index : UniIndex) (free : Array UniIndex)
    (unique : KeyUnique mapping) (fresh : GeneralBorrowTagMap.Fresh mapping tag) :
    KeyUnique ⟨mapping.mapping.push (tag,index),free⟩ := by
  unfold KeyUnique
  simp only [Array.toList_push,List.map_append,List.map_cons,List.map_nil]
  apply List.nodup_append.mpr
  refine ⟨unique,by simp,?_⟩
  intro key member last singleton
  have equal : last = tag := by simpa only [List.mem_singleton] using singleton
  subst last
  obtain ⟨row,rowMember,keyEq⟩ := List.mem_map.mp member
  have different := fresh row (Array.mem_toList_iff.mp rowMember)
  rw [keyEq] at different
  exact different

end DuplicatePrefix.GeneralBorrowGcAllocator
