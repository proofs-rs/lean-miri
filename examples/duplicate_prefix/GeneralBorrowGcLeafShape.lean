import duplicate_prefix.GeneralBorrowGcLeafFold

namespace DuplicatePrefix.GeneralBorrowGcLeafShape
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcChildFold
open DuplicatePrefix.GeneralBorrowGcLeafFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem removal_other (tree : BorrowTree) (index query : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (different : query ≠ index) :
    (source_remove_useless_node tree index).1.nodes.get query = tree.nodes.get query := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,bind,pure]
  exact GeneralBorrowSparseRemoval.remove_get_other tree.nodes index query different

private theorem removal_absent (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    (source_remove_useless_node tree index).1.nodes.get index = none := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,bind,pure]
  exact GeneralBorrowFreshDeassignment.get_removed tree.nodes index

private theorem removal_capacity (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    (source_remove_useless_node tree index).1.nodes.size = tree.nodes.size := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,bind,pure]
  exact GeneralBorrowSparseRemoval.remove_size tree.nodes index

private theorem removal_shrinks (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (query : UniIndex) (value : TreeNode)
    (found : (source_remove_useless_node tree index).1.nodes.get query = some value) :
    tree.nodes.get query = some value := by
  by_cases same : query = index
  · subst query
    rw [removal_absent tree index node present] at found
    cases found
  · rw [removal_other tree index query node present same] at found
    exact found

/-- Strengthen the actual successful leaf fold with exact surviving child
membership. Previously kept indices are distinct, present and disjoint from the
pending list. Every resulting node already existed unchanged before the fold. -/
theorem accumulated (items : List UniIndex) (seed tree : BorrowTree) (root parent : UniIndex)
    (live : Array BorTag) (kept : Array UniIndex) (distinct : items.Nodup)
    (leaves : ∀ index ∈ items, ∃ node, tree.nodes.get index = some node ∧ node.children = #[])
    (keptDistinct : kept.toList.Nodup)
    (separate : ∀ index ∈ kept.toList, index ∉ items)
    (keptPresent : ∀ index ∈ kept.toList, ∃ node, tree.nodes.get index = some node) :
    ∃ after result, forIn items (none,tree,kept) (childScan seed root live parent) = (none,after,result) ∧
      after.nodes.size = tree.nodes.size ∧
      (∀ query, query ∉ items → after.nodes.get query = tree.nodes.get query) ∧
      (∀ query node, after.nodes.get query = some node → tree.nodes.get query = some node) ∧
      result.toList.Nodup ∧
      (∀ query, query ∈ result.toList ↔
        (query ∈ kept.toList ∨ query ∈ items) ∧ ∃ node, after.nodes.get query = some node) := by
  induction items generalizing tree kept with
  | nil =>
    refine ⟨tree,kept,rfl,rfl,(fun _ _ => rfl),(fun _ _ found => found),keptDistinct,?_⟩
    intro query
    constructor
    · intro member
      exact ⟨Or.inl member,keptPresent query member⟩
    · rintro ⟨member,_⟩
      simpa using member
  | cons index rest ih =>
    obtain ⟨node,present,empty⟩ := leaves index (by simp)
    have tailDistinct := (List.nodup_cons.mp distinct).2
    have notRest := (List.nodup_cons.mp distinct).1
    rw [List.forIn_cons,GeneralBorrowGcLeafFold.step seed tree root parent index live node present empty kept]
    cases held : live.contains node.tag with
    | true =>
      simp only [held,↓reduceIte,bind]
      have pushedDistinct : (kept.push index).toList.Nodup := by
        rw [Array.toList_push]
        apply List.nodup_append.mpr
        refine ⟨keptDistinct,by simp,?_⟩
        intro query member other singleton equal
        have same : other = index := by simpa using singleton
        exact separate query member (by simp [equal,same])
      have pushedSeparate : ∀ query ∈ (kept.push index).toList, query ∉ rest := by
        intro query member
        rcases (show query ∈ kept.toList ∨ query = index from by simpa using member) with old | fresh
        · exact fun bad => separate query old (by simp [bad])
        · subst query;exact notRest
      have pushedPresent : ∀ query ∈ (kept.push index).toList, ∃ value, tree.nodes.get query = some value := by
        intro query member
        rcases (show query ∈ kept.toList ∨ query = index from by simpa using member) with old | fresh
        · exact keptPresent query old
        · subst query;exact ⟨node,present⟩
      obtain ⟨after,result,done,size,outside,shrinks,nodup,members⟩ := ih tree (kept.push index) tailDistinct
        (fun query member => leaves query (by simp [member])) pushedDistinct pushedSeparate pushedPresent
      refine ⟨after,result,done,size,?_,shrinks,nodup,?_⟩
      · intro query absent
        exact outside query (fun member => absent (by simp [member]))
      · intro query
        rw [members]
        simp only [Array.toList_push,List.mem_append,List.mem_singleton,List.mem_cons,List.not_mem_nil,or_false]
        constructor
        · rintro ⟨(old | fresh) | later,found⟩
          · exact ⟨Or.inl old,found⟩
          · exact ⟨Or.inr (Or.inl fresh),found⟩
          · exact ⟨Or.inr (Or.inr later),found⟩
        · rintro ⟨old | fresh | later,found⟩
          · exact ⟨Or.inl (Or.inl old),found⟩
          · exact ⟨Or.inl (Or.inr fresh),found⟩
          · exact ⟨Or.inr later,found⟩
    | false =>
      simp only [held,↓reduceIte,bind]
      have nextLeaves : ∀ query ∈ rest, ∃ value,
          (source_remove_useless_node tree index).1.nodes.get query = some value ∧ value.children = #[] := by
        intro query member
        obtain ⟨value,lookup,empty⟩ := leaves query (by simp [member])
        have different : query ≠ index := fun same => notRest (same ▸ member)
        exact ⟨value,(removal_other tree index query node present different).trans lookup,empty⟩
      have nextKept : ∀ query ∈ kept.toList, ∃ value,
          (source_remove_useless_node tree index).1.nodes.get query = some value := by
        intro query member
        obtain ⟨value,lookup⟩ := keptPresent query member
        have different : query ≠ index := fun same => separate query member (by simp [same])
        exact ⟨value,(removal_other tree index query node present different).trans lookup⟩
      obtain ⟨after,result,done,size,outside,shrinks,nodup,members⟩ :=
        ih (source_remove_useless_node tree index).1 kept tailDistinct nextLeaves keptDistinct
          (fun query member bad => separate query member (by simp [bad])) nextKept
      have noIndex : ¬ ∃ value, after.nodes.get index = some value := by
        rintro ⟨value,lookup⟩
        have old := shrinks index value lookup
        rw [removal_absent tree index node present] at old
        cases old
      refine ⟨after,result,done,size.trans (removal_capacity tree index node present),?_,?_,nodup,?_⟩
      · intro query absent
        have different : query ≠ index := fun same => absent (by simp [same])
        exact (outside query (fun member => absent (by simp [member]))).trans
          (removal_other tree index query node present different)
      · intro query value lookup
        exact removal_shrinks tree index node present query value (shrinks query value lookup)
      · intro query
        rw [members]
        simp only [List.mem_cons]
        constructor
        · rintro ⟨old | later,found⟩
          · exact ⟨Or.inl old,found⟩
          · exact ⟨Or.inr (Or.inr later),found⟩
        · rintro ⟨old | fresh | later,found⟩
          · exact ⟨Or.inl old,found⟩
          · subst query;exact False.elim (noIndex found)
          · exact ⟨Or.inr later,found⟩

/-- Exact successful fold from an empty kept array. Resulting child indices are
precisely the still-present original items, in a duplicate-free list. -/
theorem complete (items : List UniIndex) (seed tree : BorrowTree) (root parent : UniIndex)
    (live : Array BorTag) (distinct : items.Nodup)
    (leaves : ∀ index ∈ items, ∃ node, tree.nodes.get index = some node ∧ node.children = #[]) :
    ∃ after result, forIn items (none,tree,#[]) (childScan seed root live parent) = (none,after,result) ∧
      after.nodes.size = tree.nodes.size ∧
      (∀ query, query ∉ items → after.nodes.get query = tree.nodes.get query) ∧
      (∀ query node, after.nodes.get query = some node → tree.nodes.get query = some node) ∧
      result.toList.Nodup ∧
      (∀ query, query ∈ result.toList ↔ query ∈ items ∧ ∃ node, after.nodes.get query = some node) := by
  obtain ⟨after,result,done,size,outside,shrinks,nodup,members⟩ := accumulated items seed tree root parent live #[]
    distinct leaves (by simp) (by simp) (by simp)
  exact ⟨after,result,done,size,outside,shrinks,nodup,fun query => by simpa using members query⟩

end DuplicatePrefix.GeneralBorrowGcLeafShape
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowGcLeafShape.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved GC leaf-shape dependency {dependency}"
