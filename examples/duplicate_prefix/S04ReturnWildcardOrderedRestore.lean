import duplicate_prefix.S04ReturnWildcardRestore
import duplicate_prefix.GeneralBorrowParentTagInvariant

namespace DuplicatePrefix.S04ReturnWildcardOrderedRestore
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- A node above the saved return cutoff has no exposed contributors below it:
ordered parent tags and the exposed-only highwater bound suffice. New hidden
descendants need not satisfy the original strict callback support bound. -/
theorem above_cardinality (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (tag : BorTag) (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree tag)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node)
    (above : tag.value < node.tag.value) (kind : AccessKind) :
    cardinality tree.nodes (effective location protections) index kind = 0 := by
  obtain ⟨depth⟩ := graph.depth
  have filtered : tree.nodes.entries.toList.filter (contributes tree.nodes (effective location protections) index kind) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro row member
    have found := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
    by_cases isExposed : row.2.isExposed = true
    · have notWalked : index ∉ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) row.1 := by
        intro walked
        have less := GeneralBorrowParentTagInvariant.walk_le tree order depth _ row.1 index row.2 node found present walked
        have bound := exposed row.1 row.2 found isExposed
        have a := UInt64.lt_iff_toNat_lt.mp above
        have b := UInt64.le_iff_toNat_le.mp less
        have c := UInt64.le_iff_toNat_le.mp bound
        omega
      simp [contributes,List.contains_iff_mem,notWalked]
    · have hidden : row.2.isExposed = false := by simpa using isExposed
      simp [contributes,hidden]
  simp only [cardinality,filtered,List.length_nil]

private theorem zero_classify (rootCount : Nat) (virtual : Bool) :
    classify rootCount 0 virtual true = classify rootCount 0 virtual false := by
  cases virtual <;> cases rootCount <;> simp [classify]

/-- Cutoff removal on the original callbacks needs only an exposed highwater
bound and existing parent order, even if a support includes newer hidden nodes. -/
theorem authorization (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (tag : BorTag) (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree tag)
    (root : UniIndex) (position : Nat) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Authorization tree location protections root position (some tag) kind support) :
    Authorization tree location protections root position none kind support := by
  have relations (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node) :
      residualRelation tree location protections root index node (some tag) kind position [] =
        residualRelation tree location protections root index node none kind position [] := by
    by_cases above : tag.value < node.tag.value
    · have zero := above_cardinality tree location protections graph order tag exposed index node present above kind
      simp only [residualRelation,residual_empty,aboveMaximum,above,decide_true,zero]
      exact zero_classify _ _
    · simp only [residualRelation,aboveMaximum,above,decide_false]
  refine ⟨old.rooted,old.present,old.children,old.covers,old.possible,?_,?_⟩
  · intro before after legalBefore legalAfter subset index node inside present retained
    have beforeEmpty := no_maximum_removal_empty tree location protections kind before legalBefore
    have afterEmpty := no_maximum_removal_empty tree location protections kind after legalAfter
    subst before
    subst after
    rw [←relations index node present]
    exact old.queries [] [] (empty_removal tree location protections (some tag) kind)
      (empty_removal tree location protections (some tag) kind) (by simp) index node inside present (by simp)
  · intro primary
    obtain ⟨index,node,inside,present,supported⟩ := old.witness primary
    exact ⟨index,node,inside,present,supported.1,supported.2.1,by simp⟩

theorem row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (root : UniIndex) (tag : BorTag) (node : TreeNode)
    (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree tag)
    (present : tree.nodeAt root = some node) (leaf : node.children = #[])
    (hidden : node.isExposed = false) (absent : protections.contains node.tag = false)
    (notPrimary : ∀ valid : 0 < tree.roots.size, tree.roots[0] ≠ root)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (old : DuplicatePrefixBorrowAuthorization.Row tree location protections (some root) (some root) (some tag)) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Row tree location protections none none none) := by
  refine ⟨{wildcard := fun _ => rfl,rootPath := ?_,rootPresent := ?_,cutoff := rfl,normal := ?_,callbacks := ?_}⟩
  · intro anchor impossible;cases impossible
  · intro anchor impossible;cases impossible
  · intro anchor impossible;cases impossible
  · intro position valid different
    by_cases same : tree.roots[position] = root
    · have secondary : position ≠ 0 := by intro zero;subst position;exact notPrimary valid same
      refine ⟨(fun index => index = root),?_,?_⟩
      all_goals rw [same]
      · exact S04ReturnWildcardRestore.leaf_callback tree location protections graph root node present leaf hidden position secondary .Read (possible root node present) absent
      · exact S04ReturnWildcardRestore.leaf_callback tree location protections graph root node present leaf hidden position secondary .Write (possible root node present) absent
    · obtain ⟨support,read,write⟩ := old.callbacks position valid (by simpa using Ne.symm same)
      exact ⟨support,authorization tree location protections graph order tag exposed _ position .Read support read,
        authorization tree location protections graph order tag exposed _ position .Write support write⟩

/-- Restore full wildcard permission from ordinary current child Positive and
structural facts preserved by the real hidden helper constructors. -/
theorem positive (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (root : UniIndex) (tag : BorTag) (offset len : UInt64) (node : TreeNode)
    (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree tag)
    (present : tree.nodeAt root = some node) (leaf : node.children = #[]) (parentless : node.parent = none)
    (hidden : node.isExposed = false) (absent : global.protectedTags.contains node.tag = false)
    (notPrimary : ∀ valid : 0 < tree.roots.size, tree.roots[0] ≠ root)
    (old : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags (some root) (some root) (some tag) offset len) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags none none none offset len) := by
  have member := runtime.formed.covered root node present parentless
  have nonempty : 0 < tree.roots.size := by simpa only [Array.length_toList] using List.length_pos_of_mem member
  refine ⟨{positive := old.positive,bounds := old.bounds,sourcePresent := ?_,wildcardRoot := fun _ => nonempty,rows := ?_}⟩
  · intro anchor impossible;cases impossible
  · intro position valid nonzero start stop
    obtain ⟨oldRow⟩ := old.rows position valid nonzero start stop
    exact row tree _ global.protectedTags runtime.formed.toGraphState order root tag node exposed present leaf hidden absent notPrimary
      (runtime.possible position valid) oldRow

/-- Actual release and whole-frame endCall, using ordinary child Positive.
All later owned frame tags may be hidden and newer than the return cutoff. -/
theorem release_to_wildcard (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (allocation : AllocId) (tag : BorTag) (root : UniIndex) (offset len : UInt64)
    (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree tag)
    (old : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags (some root) (some root) (some tag) offset len)
    (node : TreeNode) (present : tree.nodeAt root = some node)
    (sameTag : node.tag = tag) (parentless : node.parent = none) (leaf : node.children = #[])
    (hidden : node.isExposed = false) (tagged : tree.indexOfTag tag = some root)
    (owned : (allocation,tag) ∈ frame.protectedTags.toList)
    (hiddenFrame : S04ReturnReleaseParent.HiddenFrame tree frame)
    (notPrimary : ∀ valid : 0 < tree.roots.size, tree.roots[0] ≠ root)
    (distinct : tree.roots.toList.Nodup) (short : tree.nodes.size < 65536)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree root .Write offset (offset+len)) :
    let actual := tree.releaseProtector tag global.protectedTags
    actual.status = .Released ∧
      DuplicatePrefixBorrowContract.RuntimeFacts actual.tree (global.endCall frame) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive actual.tree (global.endCall frame).protectedTags none none none offset len) ∧
      actual.tree = {tree with locations := actual.tree.locations} ∧ actual.tree.locations.size = tree.locations.size := by
  obtain ⟨done,afterRuntime,⟨afterPositive⟩,activity,shape,capacity⟩ := GeneralBorrowBothProtectorRelease.release
    tree global runtime tag root root (some tag) offset len old node present hidden tagged distinct (fun _ _ => order) short active
  let actual := tree.releaseProtector tag global.protectedTags
  have afterPresent : actual.tree.nodeAt root = some node := by
    change actual.tree.nodes.get root = some node
    rw [congrArg BorrowTree.nodes shape]
    exact present
  have afterHidden : S04ReturnReleaseParent.HiddenFrame actual.tree frame := by
    intro row member index value found same
    have old : tree.nodeAt index = some value := by
      change actual.tree.nodes.get index = some value at found
      rw [congrArg BorrowTree.nodes shape] at found
      exact found
    exact hiddenFrame row member index value old same
  obtain ⟨finalRuntime,⟨finalPositive⟩⟩ := S04ReturnReleaseParent.end_call actual.tree global frame afterRuntime afterHidden
    (some root) (some root) (some tag) offset len afterPositive
  have absent : (global.endCall frame).protectedTags.contains node.tag = false := by
    rw [sameTag]
    exact GeneralBorrowRelease.end_call_owned_absent global frame allocation tag owned
  have nodes := congrArg BorrowTree.nodes shape
  change actual.tree.nodes = tree.nodes at nodes
  have afterOrder := GeneralBorrowParentTagInvariant.nodes_frame tree actual.tree nodes order
  have afterExposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound actual.tree tag := by
    intro index value found isExposed
    change actual.tree.nodes.get index = some value at found
    rw [congrArg BorrowTree.nodes shape] at found
    exact exposed index value found isExposed
  have afterNotPrimary : ∀ valid : 0 < actual.tree.roots.size, actual.tree.roots[0] ≠ root := by
    rw [congrArg BorrowTree.roots shape]
    exact notPrimary
  exact ⟨done,finalRuntime,positive actual.tree _ finalRuntime afterOrder root tag offset len node afterExposed afterPresent leaf
    parentless hidden absent afterNotPrimary finalPositive,shape,capacity⟩

end DuplicatePrefix.S04ReturnWildcardOrderedRestore
