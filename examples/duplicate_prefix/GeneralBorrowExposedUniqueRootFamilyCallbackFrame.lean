import duplicate_prefix.GeneralBorrowExposedUniqueRootFamilyRows
import duplicate_prefix.GeneralBorrowFreshActiveOnClean
namespace DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyCallbackFrame
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
open Lean Elab in
elab "family_activation_iterator" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowExposedConcreteLast.iterator" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected frozen family callback helper"
open Lean Elab in
elab "family_activation_fold" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowExposedLeafRootActivation.virtual_fold" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected frozen family callback helper"
open Lean Elab in
elab "family_skip_iterator" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowExposedKnownRootWriteAccess.iterator" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected frozen family callback helper"
open Lean Elab in
elab "family_skip_fold" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowExposedLeafRootUniqueSkip.virtual_fold" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected frozen family callback helper"
open Lean Elab in
elab "family_skip_virtual" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowExposedLeafRootUniqueSkip.virtual_unique" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected frozen family callback helper"
theorem activate (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
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
    source_access_location accessed=(tree.performNormalAccessAt location anchor .Write protections .VisitChildrenOfAccessed).location ∧
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
  have tail := family_activation_fold tree middle protections extras anchorNode.tag (by
    intro root member
    obtain ⟨node,present,leaf,exposed,stored,cache,bound⟩ := old root member
    exact ⟨node,present,leaf,(normal.2.2.2.2 root node present (oldDifferent root node present exposed)).trans stored,
      by rw [normal.2.2.2.1];exact cache,bound⟩)
  have actual := family_activation_iterator tree location middle head anchor anchorNode extras .Write protections range roots
    (Ne.symm headDifferent) anchorPresent normal.1 normal.2.1 normal.2.2.1 first
    (by intro root member;obtain ⟨node,present,leaf,exposed,_⟩:=old root member;exact oldDifferent root node present exposed) tail
  refine ⟨actual.1,actual.2,?_,?_,?_⟩
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

theorem skip (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (head anchor : UniIndex) (headNode anchorNode : TreeNode) (extras : List UniIndex) (range : ByteRange)
    (roots : tree.roots=(head::(extras++[anchor])).toArray)
    (headPresent : tree.nodeAt head=some headNode) (headLeaf : headNode.children=#[]) (headExposed : headNode.isExposed=true)
    (headStored : location.perms.get head=some GeneralBorrowWildcardLeaf.unique)
    (headCache : location.exposedCache.nodes.get head=some (⟨1,1⟩:ExposedCacheNode))
    (headBound : headNode.tag.value≤anchorNode.tag.value)
    (anchorPresent : tree.nodeAt anchor=some anchorNode) (anchorParent : anchorNode.parent=none)
    (anchorLeaf : anchorNode.children=#[]) (anchorHidden : anchorNode.isExposed=false)
    (anchorStored : location.perms.get anchor=some GeneralBorrowWildcardLeaf.unique)
    (fits : tree.nodes.data.size≤4294967296)
    (old : ∀ root∈extras,∃ node,tree.nodeAt root=some node ∧ node.children=#[] ∧ node.isExposed=true ∧
      location.perms.get root=some GeneralBorrowWildcardLeaf.unique ∧
      location.exposedCache.nodes.get root=some (⟨1,1⟩:ExposedCacheNode) ∧ node.tag.value≤anchorNode.tag.value) :
    let accessed := source_tree_access_at tree location (some anchor) .Write protections .SkipChildrenOfAccessed range
    source_access_location accessed=(tree.performNormalAccessAt location anchor .Write protections .SkipChildrenOfAccessed).location ∧
    source_access_status accessed=none ∧
      (source_access_location accessed).perms.get anchor=some GeneralBorrowWildcardLeaf.unique ∧
      (source_access_location accessed).exposedCache=location.exposedCache ∧
      ∀ root∈head::extras,(source_access_location accessed).perms.get root=location.perms.get root := by
  letI : GeneralBorrowExposedKnownRootState.Scope := ⟨fun _=>False⟩
  have localOwned : ∀ held,GeneralBorrowPermissions.AccessOwned GeneralBorrowWildcardLeaf.unique .Write .LocalAccess held := by
    intro held
    simp [GeneralBorrowPermissions.AccessOwned,GeneralBorrowPermissions.Owned,GeneralBorrowPermissions.LocalOwned,GeneralBorrowWildcardLeaf.unique,LocationState.possible]
  have normal := GeneralBorrowIsolatedLeafNormal.access tree location protections anchor anchorNode .Write .SkipChildrenOfAccessed
    anchorPresent anchorParent anchorLeaf anchorHidden GeneralBorrowWildcardLeaf.unique anchorStored localOwned
  let middle := (tree.performNormalAccessAt location anchor .Write protections .SkipChildrenOfAccessed).location
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
  have tail := family_skip_fold tree middle protections extras anchorNode.tag (by
    intro root member
    obtain ⟨node,present,leaf,exposed,stored,cache,bound⟩ := old root member
    exact ⟨node,present,leaf,(normal.2.2.2.2 root node present (oldDifferent root node present exposed)).trans stored,
      by rw [normal.2.2.2.1];exact cache,bound⟩)
  have minimum : source_min_exposed tree anchor=none := by
    apply GeneralBorrowExposedKnownRootMinimum.min_none tree anchor (fun index=>index=anchor) rfl
    · intro index node same present child member
      subst index
      have equal := Option.some.inj (present.symm.trans anchorPresent)
      subst node
      rw [anchorLeaf] at member
      cases member
    · intro index node same present
      subst index
      have equal := Option.some.inj (present.symm.trans anchorPresent)
      subst node
      exact anchorHidden
  have completed : GeneralBorrowExposedKnownRootWriteSchedule.run tree (extras++[anchor]) anchor middle anchorNode.tag protections=⟨middle,.Completed⟩ := by
    have fold : ∀ schedule : List UniIndex,(∀ root∈schedule,root∈extras) →
        GeneralBorrowExposedKnownRootWriteSchedule.run tree (schedule++[anchor]) anchor middle anchorNode.tag protections=⟨middle,.Completed⟩ := by
      intro schedule
      induction schedule with
      | nil => intro _;simp [GeneralBorrowExposedKnownRootWriteSchedule.run]
      | cons root rest ih =>
        intro subset
        obtain ⟨node,present,leaf,exposed,stored,cache,bound⟩ := old root (subset root (by simp))
        have different := oldDifferent root node present exposed
        have called := family_skip_virtual tree middle protections root node anchorNode.tag present leaf
          ((normal.2.2.2.2 root node present different).trans stored) (by rw [normal.2.2.2.1];exact cache) bound
        simpa only [List.cons_append,GeneralBorrowExposedKnownRootWriteSchedule.run,different,↓reduceIte,called,beq_self_eq_true] using
          ih (fun query member=>subset query (by simp [member]))
    exact fold extras (fun _ member=>member)
  have actual := family_skip_iterator tree location middle middle anchor anchor head anchorNode (extras++[anchor]) protections .SkipChildrenOfAccessed range
    roots anchorPresent normal.1 normal.2.1 normal.2.2.1 minimum
    (by simpa only [show ¬anchor=head from Ne.symm headDifferent,↓reduceIte] using first) completed
  refine ⟨actual.1,actual.2,?_,?_,?_⟩
  · rw [actual.1]
    exact GeneralBorrowIsolatedLeafUniqueStable.unique tree location protections anchor anchorNode .SkipChildrenOfAccessed
      anchorPresent anchorParent anchorLeaf anchorStored fits
  · rw [actual.1]
    exact normal.2.2.2.1
  · intro root member
    rw [actual.1]
    rcases List.mem_cons.mp member with same | member
    · subst root;exact normal.2.2.2.2 head headNode headPresent headDifferent
    · obtain ⟨node,present,leaf,exposed,_⟩ := old root member
      exact normal.2.2.2.2 root node present (oldDifferent root node present exposed)

end DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyCallbackFrame
