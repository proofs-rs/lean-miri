import duplicate_prefix.GeneralBorrowGeneratedStarShape
import duplicate_prefix.GeneralBorrowFreshMetadataChildSharedReuse

namespace DuplicatePrefix.GeneralBorrowGeneratedReuseStarShape
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGeneratedStarShape (Star of_nodes shaped)
open DuplicatePrefix.GeneralBorrowFreshMetadataChildSharedReuse
open DuplicatePrefix.GeneralBorrowFreshMetadataChildReuseGraph
open DuplicatePrefix.GeneralBorrowFreshGraph (attached updatedParent)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual reuse-stage node mutations extend a star by one fresh leaf. -/
theorem attached_star (tree : BorrowTree) (root : UniIndex) (rootNode : TreeNode)
    (index : UniIndex) (leaf : TreeNode) (good : Star tree root rootNode)
    (vacant : tree.nodes.get index = none) (parent : leaf.parent = some root)
    (empty : leaf.children = #[]) :
    Star (attached tree index root rootNode leaf) root (updatedParent rootNode index) := by
  have notNew : root ≠ index := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes index root rootNode vacant good.present
  refine ⟨parent_lookup tree index root rootNode leaf vacant good.present,good.parentless,?_,?_,?_⟩
  · intro query node present different
    by_cases fresh : query = index
    · subst query
      rw [new_lookup tree index root rootNode leaf vacant good.present] at present
      cases present
      exact ⟨parent,empty⟩
    · rw [other_lookup tree index root query rootNode leaf vacant good.present different fresh] at present
      exact good.leaves query node present different
  · simp only [updatedParent,Array.toList_push]
    apply List.nodup_append.mpr
    refine ⟨good.distinct,by simp,?_⟩
    intro query member other singleton equal
    have same : other = index := by simpa only [List.mem_singleton] using singleton
    obtain ⟨node,present⟩ := (good.children query).mp member |>.2
    change tree.nodes.get query = some node at present
    rw [equal,same,vacant] at present
    cases present
  · intro query
    simp only [updatedParent,Array.toList_push,List.mem_append,List.mem_singleton]
    constructor
    · intro member
      rcases member with old | fresh
      · obtain ⟨different,node,present⟩ := (good.children query).mp old
        exact ⟨different,old_present tree index root query rootNode leaf node vacant good.present present⟩
      · subst query
        exact ⟨Ne.symm notNew,leaf,new_lookup tree index root rootNode leaf vacant good.present⟩
    · rintro ⟨different,node,present⟩
      by_cases fresh : query = index
      · exact Or.inr fresh
      · rw [other_lookup tree index root query rootNode leaf vacant good.present different fresh] at present
        exact Or.inl ((good.children query).mpr ⟨different,node,present⟩)

attribute [local irreducible] GeneralBorrowFreshMetadataChildSharedReuse.result GeneralBorrowFreshMetadataChildSharedReuse.stage

/-- A real shared vacant-slot reuse retains exact star topology after the actual SIFA. -/
theorem reuse_star (input : Input) (good : Star input.tree input.parent input.parentNode) :
    ∃ node, Star (result input) input.parent node := by
  have known := attached_star input.tree input.parent input.parentNode (index input)
    (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) good input.vacant rfl rfl
  have nodesEq : (stage input).nodes =
      (attached input.tree (index input) input.parent input.parentNode
        (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent)).nodes := by
    unfold stage GeneralBorrowFreshMetadataChildAttach.staged
    rfl
  have staged := of_nodes _ (stage input) input.parent (updatedParent input.parentNode (index input)) nodesEq known
  exact shaped (stage input) (result input) input.parent (updatedParent input.parentNode (index input)) (shape input) staged

end DuplicatePrefix.GeneralBorrowGeneratedReuseStarShape
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowGeneratedReuseStarShape." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated reuse star dependency {dependency}"
