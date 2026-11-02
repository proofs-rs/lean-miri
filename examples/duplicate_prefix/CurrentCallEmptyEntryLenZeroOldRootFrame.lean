import duplicate_prefix.S03EmptySharedFrame
import duplicate_prefix.GeneralBorrowSifaOutsidePath

namespace DuplicatePrefix.CurrentCallEmptyEntryLenZeroOldRootFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowSharedAuthorizationGeometry
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

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

private theorem stage_old {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag)
    (query : UniIndex) (node : TreeNode) (present : tree.nodes.get query = some node) :
    ∃ next, input.stage.nodes.get query = some next ∧ next.parent = node.parent := by
  have lookup := S04ZeroReadSharedAttach.old_lookup tree input.index input.parent input.parentNode
    (GeneralBorrowFreshAnchor.sharedNode tag input.parent) input.vacant input.present query node present
  change input.stage.nodes.get query = _ at lookup
  refine ⟨S04ZeroReadSharedAttach.liftNode input.parent input.index query node,lookup,?_⟩
  unfold S04ZeroReadSharedAttach.liftNode
  split <;> rfl

private theorem frame {tree : BorrowTree} {parentTag tag : BorTag}
    (input : EmptyForestSharedPool.Input tree parentTag tag)
    (query : UniIndex) (node : TreeNode) (present : tree.nodes.get query = some node)
    (different : query ≠ input.parent) (outside : ¬Path input.stage query input.parent) :
    input.after.nodes.get query = tree.nodes.get query := by
  have lookup := S04ZeroReadSharedAttach.old_lookup tree input.index input.parent input.parentNode
    (GeneralBorrowFreshAnchor.sharedNode tag input.parent) input.vacant input.present query node present
  have exactStage : input.stage.nodes.get query = tree.nodes.get query := by
    change input.stage.nodes.get query = _ at lookup
    simpa only [S04ZeroReadSharedAttach.liftNode,different,ite_false,present] using lookup
  obtain ⟨parent,found,_⟩ := stage_old input input.parent input.parentNode input.present
  let depth := GeneralBorrowFreshMetadata.parent_depth input.after input.stage
    (GeneralBorrowSifaView.preserves input.stage input.parent .Read).symm input.afterDepth
  have observed := congrArg Prod.fst (GeneralBorrowSifaOutsidePath.frame input.stage depth input.parent parent found
    query outside .Read)
  change input.after.nodes.get query = input.stage.nodes.get query at observed
  exact observed.trans exactStage

/-- The two actual zero shared helpers keep every full old node on another
original physical component. Their real SIFA updates on q and h1 remain. -/
theorem nodes {tree : BorrowTree} {parentTag tag1 tag2 : BorTag}
    (first : EmptyForestSharedPool.Input tree parentTag tag1)
    (second : EmptyForestSharedPool.Input first.after tag1 tag2)
    (secondParent : second.parent = first.index)
    (parentless : first.parentNode.parent = none)
    (root query : UniIndex) (different : root ≠ first.parent)
    (path : Path tree root query) :
    second.after.nodes.get query = tree.nodes.get query := by
  obtain ⟨node,present⟩ := path.present
  have notQ : query ≠ first.parent := by
    intro same
    subst query
    exact different (root_path first.present parentless path)
  obtain ⟨stageQ,stageQAt,stageQParent⟩ := stage_old first first.parent first.parentNode first.present
  have outsideFirst : ¬Path first.stage query first.parent := by
    intro bad
    exact notQ (root_path stageQAt (stageQParent.trans parentless) bad)
  have firstFrame := frame first query node present notQ outsideFirst
  have middleAt : first.after.nodes.get query = some node := firstFrame.trans present
  have notH1 : query ≠ first.index := by
    intro same
    rw [same,first.vacant] at present
    cases present
  obtain ⟨middleQ,middleQAt,_,middleQParent,_⟩ :=
    S03EmptySharedFrame.old_node first first.parent first.parentNode first.present
  obtain ⟨lastQ,lastQAt,lastQParent⟩ := stage_old second first.parent middleQ middleQAt
  have lastQNone : lastQ.parent = none := lastQParent.trans (middleQParent.trans parentless)
  have childParent : second.parentNode.parent = some first.parent := by
    obtain ⟨child,found,_,parent,_,_,_⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields
      first.stage first.parent .Read first.index (GeneralBorrowFreshAnchor.sharedNode tag1 first.parent) first.stage_new
    change first.after.nodeAt first.index = some child at found
    have same := Option.some.inj (found.symm.trans (by simpa only [secondParent] using second.present))
    subst child
    exact parent
  obtain ⟨lastH1,lastH1At,lastH1Parent⟩ := stage_old second second.parent second.parentNode second.present
  have outsideSecond : ¬Path second.stage query second.parent := by
    intro bad
    cases bad with
    | refl => exact notH1 secondParent
    | step earlier actual found edge =>
      have same := Option.some.inj (found.symm.trans lastH1At)
      subst actual
      have parentEq := lastH1Parent.trans childParent
      rw [parentEq] at edge
      cases edge
      exact notQ (root_path lastQAt lastQNone earlier)
  exact (frame second query node middleAt (by simpa only [secondParent] using notH1) outsideSecond).trans firstFrame

theorem roots {tree : BorrowTree} {parentTag tag1 tag2 : BorTag}
    (first : EmptyForestSharedPool.Input tree parentTag tag1)
    (second : EmptyForestSharedPool.Input first.after tag1 tag2) :
    second.after.roots = tree.roots := by
  simpa only [EmptyForestSharedPool.Input.stage,GeneralBorrowFreshGraph.attached] using
    (GeneralBorrowFreshMetadata.roots second.stage second.after
    (GeneralBorrowSifaView.preserves second.stage second.parent .Read)).trans
    (GeneralBorrowFreshMetadata.roots first.stage first.after
      (GeneralBorrowSifaView.preserves first.stage first.parent .Read))

/-- Original support paths extend through the actual helper trees; only
parent metadata is used, so real SIFA and child-list changes are retained. -/
theorem paths {tree : BorrowTree} {parentTag tag1 tag2 : BorTag}
    (first : EmptyForestSharedPool.Input tree parentTag tag1)
    (second : EmptyForestSharedPool.Input first.after tag1 tag2)
    (root query : UniIndex) (path : Path tree root query) :
    Path second.after root query := by
  have middle : Path first.after root query := by
    apply path_extension tree first.after _ root query path
    intro index node present
    obtain ⟨next,found,_,parent,_⟩ := S03EmptySharedFrame.old_node first index node present
    exact ⟨next,found,parent⟩
  apply path_extension first.after second.after _ root query middle
  intro index node present
  obtain ⟨next,found,_,parent,_⟩ := S03EmptySharedFrame.old_node second index node present
  exact ⟨next,found,parent⟩

end DuplicatePrefix.CurrentCallEmptyEntryLenZeroOldRootFrame

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryLenZeroOldRootFrame" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved old-root frame dependency {dependency}"
