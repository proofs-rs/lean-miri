import duplicate_prefix.GeneralBorrowIsolatedLeafActivation
import duplicate_prefix.GeneralBorrowExposedConcreteLast
namespace DuplicatePrefix.GeneralBorrowExposedLeafRootActivation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
open Lean Elab in
elab "leaf_root_source_iterator" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowExposedConcreteLast.iterator" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected frozen concrete-root source iterator"

private theorem virtual_unique (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (node : TreeNode) (maximum : BorTag)
    (present : tree.nodeAt root=some node) (leaf : node.children=#[])
    (stored : location.perms.get root=some GeneralBorrowWildcardLeaf.unique)
    (cache : location.exposedCache.nodes.get root=some (⟨1,1⟩:ExposedCacheNode))
    (bound : node.tag.value≤maximum.value) :
    tree.performWildcardAccessAt location root (some maximum) .Write protections true=⟨location,.Completed⟩ := by
  have positive : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache root .Write≠0 := by
    simp [GeneralBorrowWildcardRelatednessBounds.count,cache]
  have cutoff : GeneralBorrowWildcardVirtualLeaf.onlyForeign node (some maximum)=false := by
    simp only [GeneralBorrowWildcardVirtualLeaf.onlyForeign]
    exact decide_eq_false (UInt64.not_lt.mpr bound)
  rw [GeneralBorrowWildcardVirtualLeaf.either_access tree location root node (some maximum) .Write protections present leaf positive cutoff]
  simp only [GeneralBorrowWildcardVirtualLeaf.materialized,UniValMap.orInsert,stored]

private theorem virtual_fold (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (roots : List UniIndex) (maximum : BorTag)
    (data : ∀ root∈roots,∃ node,tree.nodeAt root=some node ∧ node.children=#[] ∧
      location.perms.get root=some GeneralBorrowWildcardLeaf.unique ∧
      location.exposedCache.nodes.get root=some (⟨1,1⟩:ExposedCacheNode) ∧ node.tag.value≤maximum.value) :
    GeneralBorrowWildcardVirtualLeafFold.run tree roots location (some maximum) .Write protections=⟨location,.Completed⟩ := by
  induction roots with
  | nil => rfl
  | cons root rest ih =>
    obtain ⟨node,present,leaf,stored,cache,bound⟩ := data root (by simp)
    have first := virtual_unique tree location protections root node maximum present leaf stored cache bound
    simpa only [GeneralBorrowWildcardVirtualLeafFold.run,first,beq_self_eq_true,↓reduceIte] using
      ih (fun query member=>data query (by simp [member]))

/-- Actual full source callback activates a new isolated reserved root to exact
Unique while preserving every old exposed Unique leaf and its exact counters.
The number of older roots is arbitrary and no final Unique/cache premise is used. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (head anchor : UniIndex) (headNode anchorNode : TreeNode) (extras : List UniIndex) (range : ByteRange)
    (roots : tree.roots=(head::(extras++[anchor])).toArray)
    (headPresent : tree.nodeAt head=some headNode) (headLeaf : headNode.children=#[]) (headExposed : headNode.isExposed=true)
    (headStored : location.perms.get head=some GeneralBorrowWildcardLeaf.unique)
    (headCache : location.exposedCache.nodes.get head=some (⟨1,1⟩:ExposedCacheNode))
    (headBound : headNode.tag.value≤anchorNode.tag.value)
    (anchorPresent : tree.nodeAt anchor=some anchorNode) (anchorParent : anchorNode.parent=none)
    (anchorLeaf : anchorNode.children=#[]) (anchorHidden : anchorNode.isExposed=false)
    (anchorStored : location.perms.get anchor=some GeneralBorrowFreshChild.inside)
    (fits : tree.nodes.data.size≤4294967296)
    (old : ∀ root∈extras,∃ node,tree.nodeAt root=some node ∧ node.children=#[] ∧ node.isExposed=true ∧
      location.perms.get root=some GeneralBorrowWildcardLeaf.unique ∧
      location.exposedCache.nodes.get root=some (⟨1,1⟩:ExposedCacheNode) ∧ node.tag.value≤anchorNode.tag.value) :
    let accessed := source_tree_access_at tree location (some anchor) .Write protections .VisitChildrenOfAccessed range
    source_access_status accessed=none ∧
      (source_access_location accessed).perms.get anchor=some GeneralBorrowWildcardLeaf.unique ∧
      (source_access_location accessed).exposedCache=location.exposedCache ∧
      ∀ root∈head::extras,(source_access_location accessed).perms.get root=location.perms.get root := by
  have localOwned := fun held=>GeneralBorrowPermissions.fresh_mutable_owned .None true held
  have normal := GeneralBorrowIsolatedLeafNormal.access tree location protections anchor anchorNode .Write .VisitChildrenOfAccessed
    anchorPresent anchorParent anchorLeaf anchorHidden GeneralBorrowFreshChild.inside anchorStored localOwned
  let middle := (tree.performNormalAccessAt location anchor .Write protections .VisitChildrenOfAccessed).location
  have oldDifferent : ∀ root node,tree.nodeAt root=some node → node.isExposed=true → root≠anchor := by
    intro root node present exposed same
    subst root
    have equal := Option.some.inj (present.symm.trans anchorPresent)
    subst node
    rw [anchorHidden] at exposed
    cases exposed
  have headDifferent := oldDifferent head headNode headPresent headExposed
  have first : tree.performWildcardAccessAt middle head (some anchorNode.tag) .Write protections false=⟨middle,.Completed⟩ :=
    GeneralBorrowWildcardLeaf.access tree middle head headNode anchorNode.tag .Write protections
      ⟨headPresent,headLeaf,headExposed,(normal.2.2.2.2 head headNode headPresent headDifferent).trans headStored,
        by rw [normal.2.2.2.1];exact headCache,headBound⟩
  have tail := virtual_fold tree middle protections extras anchorNode.tag (by
    intro root member
    obtain ⟨node,present,leaf,exposed,stored,cache,bound⟩ := old root member
    exact ⟨node,present,leaf,(normal.2.2.2.2 root node present (oldDifferent root node present exposed)).trans stored,
      by rw [normal.2.2.2.1];exact cache,bound⟩)
  have actual := leaf_root_source_iterator tree location middle head anchor anchorNode extras .Write protections range roots
    (Ne.symm headDifferent) anchorPresent normal.1 normal.2.1 normal.2.2.1 first
    (by intro root member;obtain ⟨node,present,leaf,exposed,_⟩:=old root member;exact oldDifferent root node present exposed) tail
  refine ⟨actual.2,?_,?_,?_⟩
  · rw [actual.1]
    exact GeneralBorrowIsolatedLeafActivation.unique tree location protections anchor anchorNode .VisitChildrenOfAccessed
      anchorPresent anchorParent anchorLeaf anchorStored fits
  · rw [actual.1]
    exact normal.2.2.2.1
  · intro root member
    rw [actual.1]
    rcases List.mem_cons.mp member with same | member
    · subst root;exact normal.2.2.2.2 head headNode headPresent headDifferent
    · obtain ⟨node,present,leaf,exposed,_⟩ := old root member
      exact normal.2.2.2.2 root node present (oldDifferent root node present exposed)
end DuplicatePrefix.GeneralBorrowExposedLeafRootActivation
