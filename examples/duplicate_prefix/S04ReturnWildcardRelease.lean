import duplicate_prefix.S04ReturnWildcardReleaseScan
import duplicate_prefix.S04ReturnWildcardRestore

namespace DuplicatePrefix.S04ReturnWildcardRelease
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual hidden-root release preserves the scoped callback packet, including
the old supporters' cutoff bounds. -/
theorem release (tree : BorrowTree) (global : GlobalState)
    (before : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (anchor selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (positive : GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags anchor selected maximum offset len)
    (node : TreeNode) (present : tree.nodeAt anchor = some node) (hidden : node.isExposed = false)
    (tagged : tree.indexOfTag tag = some anchor) (distinct : tree.roots.toList.Nodup)
    (short : tree.nodes.size < 65536)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Write offset (offset+len)) :
    let actual := tree.releaseProtector tag global.protectedTags
    actual.status = .Released ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
      Nonempty (GeneralBorrowFreshRootScopedRow.Positive actual.tree global.protectedTags anchor selected maximum offset len) ∧
      actual.tree = {tree with locations := actual.tree.locations} ∧ actual.tree.locations.size = tree.locations.size := by
  have fits : offset.toNat+len.toNat < 2^64 := Nat.lt_of_le_of_lt positive.base.bounds tree.locations.size.bytes.toNat_lt
  have sum : (offset+len).toNat = offset.toNat+len.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  have nonempty : offset.toNat < (offset+len).toNat := by rw [sum];have p:=positive.base.positive;omega
  have runtime : GeneralRangeMapState.Every (GeneralBorrowSnapshotWildcardRangeBoth.Runtime tree global.protectedTags) tree.locations := by
    intro position valid
    exact ⟨before.coherent position valid,before.formed.profile position valid,before.possible position valid⟩
  obtain ⟨done,frame,rows,allRuntime,activity,well,capacity⟩ := S04ReturnWildcardReleaseScan.release tree global.protectedTags
    tag anchor selected maximum offset (offset+len) nonempty before.formed.toGraphState node present hidden distinct short
    tagged active before.formed.well runtime positive.rows
  let actual := tree.releaseProtector tag global.protectedTags
  have graph := GeneralBorrowStructuralHistoryState.graph_locations tree actual.tree.locations before.formed.toGraphState
  rw [←frame] at graph
  have finalRuntime : DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global := by
    refine ⟨⟨⟨graph,well⟩,?_⟩,?_,?_,?_⟩
    · intro position valid;exact (allRuntime position valid).profile
    · intro position valid;exact (allRuntime position valid).coherent
    · intro position valid;exact (allRuntime position valid).possible
    · refine ⟨?_,before.below.protectors⟩
      rw [congrArg BorrowTree.tagMapping frame]
      exact before.below.mapping
  have baseRows : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Row actual.tree location global.protectedTags
        (some anchor) (some selected) (some maximum))) offset (offset+len) actual.tree.locations := by
    intro position valid nonzero start stop
    obtain ⟨row⟩ := rows position valid nonzero start stop
    exact ⟨row.base⟩
  refine ⟨done,finalRuntime,⟨⟨?_,rows⟩⟩,frame,capacity⟩
  refine ⟨positive.base.positive,?_,?_,(by intro impossible;cases impossible),baseRows⟩
  · rw [capacity];exact positive.base.bounds
  · intro source same
    have same : source = anchor := Option.some.inj same.symm
    subst source
    refine ⟨node,?_⟩
    change actual.tree.nodes.get anchor = some node
    rw [congrArg BorrowTree.nodes frame]
    exact present

/-- Real endCall removes hidden protectors while retaining the same explicit
old-root support choices. -/
theorem end_call (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (hidden : S04ReturnReleaseParent.HiddenFrame tree frame)
    (anchor selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (positive : GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags anchor selected maximum offset len) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree (global.endCall frame) ∧
      Nonempty (GeneralBorrowFreshRootScopedRow.Positive tree (global.endCall frame).protectedTags
        anchor selected maximum offset len) := by
  obtain ⟨after,⟨base⟩⟩ := S04ReturnReleaseParent.end_call tree global frame runtime hidden
    (some anchor) (some selected) (some maximum) offset len positive.base
  have weaken := GeneralBorrowRelease.end_call_weakens global frame
  have same := S04ReturnReleaseParent.exposed_frame tree global frame hidden
  refine ⟨after,⟨⟨base,?_⟩⟩⟩
  intro position valid nonzero start stop
  obtain ⟨oldRow⟩ := positive.rows position valid nonzero start stop
  obtain ⟨baseRow⟩ := base.rows position valid nonzero start stop
  refine ⟨⟨baseRow,oldRow.exposed,?_⟩⟩
  intro index bounded different
  obtain ⟨support,bound,read,write⟩ := oldRow.callbacks index bounded different
  exact ⟨support,bound,
    GeneralBorrowHiddenProtectorRowWeakens.authorization tree _ _ _ weaken same _ _ _ _ _ read,
    GeneralBorrowHiddenProtectorRowWeakens.authorization tree _ _ _ weaken same _ _ _ _ _ write⟩

/-- Actual return-root release and whole-frame endCall restore the original
wildcard destination. Other hidden frame protectors are allowed. -/
theorem release_to_wildcard (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (allocation : AllocId) (tag : BorTag) (root : UniIndex) (offset len : UInt64)
    (positive : GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags root root tag offset len)
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
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive actual.tree (global.endCall frame).protectedTags
        none none none offset len) ∧
      actual.tree = {tree with locations := actual.tree.locations} ∧ actual.tree.locations.size = tree.locations.size := by
  obtain ⟨done,afterRuntime,⟨afterPositive⟩,shape,capacity⟩ := release tree global runtime tag root root tag offset len
    positive node present hidden tagged distinct short active
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
  obtain ⟨finalRuntime,⟨finalPositive⟩⟩ := end_call actual.tree global frame afterRuntime afterHidden root root tag offset len afterPositive
  have absent : (global.endCall frame).protectedTags.contains node.tag = false := by
    rw [sameTag]
    exact GeneralBorrowRelease.end_call_owned_absent global frame allocation tag owned
  have afterNotPrimary : ∀ valid : 0 < actual.tree.roots.size, actual.tree.roots[0] ≠ root := by
    rw [congrArg BorrowTree.roots shape]
    exact notPrimary
  exact ⟨done,finalRuntime,S04ReturnWildcardRestore.positive actual.tree _ finalRuntime root tag offset len node
    afterPresent leaf parentless hidden absent afterNotPrimary finalPositive,shape,capacity⟩

end DuplicatePrefix.S04ReturnWildcardRelease
