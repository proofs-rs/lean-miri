import duplicate_prefix.CurrentCallEmptyEntryLenZeroOldRootFrame

namespace DuplicatePrefix.CurrentCallEmptyEntryLenZeroSelectedPath
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

private theorem back {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag) (index : UniIndex) (node : TreeNode)
    (present : input.after.nodes.get index = some node) :
    (index = input.index ∧ node.parent = some input.parent) ∨
      ∃ old,tree.nodes.get index = some old ∧ node.parent = old.parent := by
  obtain ⟨staged,found,_,parent,_,_⟩ := GeneralBorrowFreshMetadata.node_fields input.after input.stage
    (GeneralBorrowSifaView.preserves input.stage input.parent .Read).symm index node present
  by_cases fresh : index = input.index
  · left
    refine ⟨fresh,?_⟩
    subst index
    have same := Option.some.inj (found.symm.trans input.stage_new)
    rw [←parent,same]
    rfl
  · right
    by_cases isParent : index = input.parent
    · subst index
      have atParent := S04ZeroReadSharedAttach.old_lookup tree input.index input.parent input.parentNode
        (GeneralBorrowFreshAnchor.sharedNode tag input.parent) input.vacant input.present input.parent input.parentNode input.present
      change input.stage.nodes.get input.parent = _ at atParent
      have same := Option.some.inj (found.symm.trans atParent)
      refine ⟨input.parentNode,input.present,?_⟩
      rw [←parent,same]
      simp only [S04ZeroReadSharedAttach.liftNode,ite_true]
    · change ((tree.nodes.insert input.index (GeneralBorrowFreshAnchor.sharedNode tag input.parent)).insert
        input.parent (GeneralBorrowFreshGraph.updatedParent input.parentNode input.index)).get index = some staged at found
      rw [GeneralBorrowFreshLocation.get_other _ _ _ _ isParent,
        GeneralBorrowFreshLocation.get_other _ _ _ _ fresh] at found
      exact ⟨staged,found,parent.symm⟩

private theorem root_path {tree : BorrowTree} {root query : UniIndex} {node : TreeNode}
    (present : tree.nodes.get query = some node) (parentless : node.parent = none)
    (path : Path tree root query) : root = query := by
  cases path with
  | refl => rfl
  | step earlier actual found edge =>
    have same := Option.some.inj (found.symm.trans present)
    subst actual
    rw [parentless] at edge
    cases edge

/-- A current path from an old component disjoint from q still names an old
live node and the original physical path after both actual zero helpers. -/
theorem paths {tree : BorrowTree} {parentTag tag1 tag2 : BorTag}
    (first : EmptyForestSharedPool.Input tree parentTag tag1)
    (second : EmptyForestSharedPool.Input first.after tag1 tag2)
    (secondParent : second.parent = first.index) (parentless : first.parentNode.parent = none)
    (root : UniIndex) (rootNode : TreeNode) (rootPresent : tree.nodes.get root = some rootNode)
    (different : root ≠ first.parent) (query : UniIndex) (path : Path second.after root query) :
    ∃ node,tree.nodes.get query = some node ∧ Path tree root query := by
  induction path with
  | refl => exact ⟨rootNode,rootPresent,.refl root rootNode rootPresent⟩
  | @step parent child earlier node present edge ih =>
    obtain ⟨parentNode,parentAt,parentPath⟩ := ih
    rcases back second child node present with ⟨fresh,parentEdge⟩ | ⟨middle,middleAt,parentMiddle⟩
    · have equal : parent = first.index := (Option.some.inj (edge.symm.trans parentEdge)).trans secondParent
      rw [equal,first.vacant] at parentAt
      cases parentAt
    · rcases back first child middle middleAt with ⟨fresh,parentEdge⟩ | ⟨old,oldAt,parentOld⟩
      · have equal : parent = first.parent := Option.some.inj (edge.symm.trans (parentMiddle.trans parentEdge))
        subst parent
        exact False.elim (different (root_path first.present parentless parentPath))
      · exact ⟨old,oldAt,.step parentPath old oldAt ((parentMiddle.trans parentOld).symm.trans edge)⟩

end DuplicatePrefix.CurrentCallEmptyEntryLenZeroSelectedPath

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryLenZeroSelectedPath" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved selected path dependency {dependency}"
