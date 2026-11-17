import duplicate_prefix.GeneralBorrowBothProtectorRelease
import duplicate_prefix.GeneralBorrowHiddenProtectorRowWeakens
import duplicate_prefix.GeneralBorrowParentPositiveReanchor

namespace DuplicatePrefix.S04ReturnReleaseParent
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A frame can own tags in other allocations too. Only exclusion of exposed
nodes in this allocation is needed when its actual endCall table is installed. -/
def HiddenFrame (tree : BorrowTree) (frame : FrameState) : Prop :=
  ∀ row ∈ frame.protectedTags.toList, ∀ index node,
    tree.nodeAt index = some node → node.tag = row.2 → node.isExposed = false

private theorem fold_get (rows : List (AllocId × BorTag)) (tags : ProtectedTags) (query : BorTag)
    (different : ∀ row ∈ rows, query ≠ row.2) :
    (rows.foldl (fun table row => table.remove row.2) tags).get query = tags.get query := by
  induction rows generalizing tags with
  | nil => rfl
  | cons row rest ih =>
    rw [List.foldl_cons,ih (tags.remove row.2) (by intro other member;exact different other (by simp [member]))]
    exact GeneralBorrowProtectorCacheMap.remove_other tags row.2 query (different row (by simp))

private theorem fold_member (rows : List (AllocId × BorTag)) (tags : ProtectedTags)
    (entry : BorTag × ProtectorKind)
    (member : entry ∈ (rows.foldl (fun table row => table.remove row.2) tags).entries) :
    entry ∈ tags.entries := by
  induction rows generalizing tags with
  | nil => exact member
  | cons row rest ih =>
    have prior := ih (tags.remove row.2) member
    exact (Array.mem_filter.mp prior).1

/-- All exposed-node protector lookups survive actual whole-frame removal. -/
theorem exposed_frame (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (hidden : HiddenFrame tree frame) :
    ∀ index node, tree.nodeAt index = some node → node.isExposed = true →
      (global.endCall frame).protectedTags.contains node.tag = global.protectedTags.contains node.tag := by
  intro index node present exposed
  have other : ∀ row ∈ frame.protectedTags.toList, node.tag ≠ row.2 := by
    intro row member same
    have h := hidden row member index node present same
    rw [exposed] at h
    contradiction
  have eqn := fold_get frame.protectedTags.toList global.protectedTags node.tag other
  simpa only [GlobalState.endCall,Array.foldl_toList,ProtectedTags.contains] using congrArg Option.isSome eqn

/-- Runtime and full source capability survive the actual endCall table for a
frame of hidden tags; no successful release is a premise of this bookkeeping lemma. -/
theorem end_call (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (hidden : HiddenFrame tree frame)
    (source selected : Option UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags source selected maximum offset len) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree (global.endCall frame) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive tree (global.endCall frame).protectedTags
        source selected maximum offset len) := by
  have weaken := GeneralBorrowRelease.end_call_weakens global frame
  have same := exposed_frame tree global frame hidden
  refine ⟨?_,GeneralBorrowHiddenProtectorRowWeakens.positive tree _ _ weaken same source selected maximum offset len positive⟩
  refine ⟨⟨runtime.formed.toState,?_⟩,?_,runtime.possible,?_⟩
  · intro position valid
    exact GeneralBorrowHiddenProtectorDropRuntime.profile tree _ _ _ weaken (runtime.formed.profile position valid)
  · intro position valid
    exact GeneralBorrowProtectorCacheMap.frame tree _ _ _ (runtime.coherent position valid) same
  · refine ⟨runtime.below.mapping,?_⟩
    intro row member
    have old := fold_member frame.protectedTags.toList global.protectedTags row
      (by simpa only [GlobalState.endCall,Array.foldl_toList] using member)
    exact runtime.below.protectors row old

/-- Real return-child release followed by the real whole-frame endCall restores
its original concrete destination parent. The one-byte window is a specialization;
no release result, future Positive, or operation success is assumed. Other hidden
frame protectors (including an empty argument in the SAME allocation) are allowed. -/
theorem release_to_parent (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (allocation : AllocId) (tag : BorTag) (child parent selected : UniIndex)
    (maximum : Option BorTag) (offset : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags
      (some child) (some selected) maximum offset 1)
    (node : TreeNode) (present : tree.nodeAt child = some node)
    (sameTag : node.tag = tag) (edge : node.parent = some parent) (hidden : node.isExposed = false)
    (tagged : tree.indexOfTag tag = some child) (owned : (allocation,tag) ∈ frame.protectedTags.toList)
    (hiddenFrame : HiddenFrame tree frame)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree child .Write offset (offset+1)) :
    let actual := tree.releaseProtector tag global.protectedTags
    actual.status = .Released ∧
      DuplicatePrefixBorrowContract.RuntimeFacts actual.tree (global.endCall frame) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive actual.tree (global.endCall frame).protectedTags
        (some parent) (some selected) maximum offset 1) ∧
      actual.tree = {tree with locations := actual.tree.locations} ∧ actual.tree.locations.size = tree.locations.size := by
  obtain ⟨done,afterRuntime,⟨afterPositive⟩,activity,shape,capacity⟩ :=
    GeneralBorrowBothProtectorRelease.release tree global runtime tag child selected maximum offset 1
      positive node present hidden tagged distinct order short active
  let actual := tree.releaseProtector tag global.protectedTags
  have afterHidden : HiddenFrame actual.tree frame := by
    intro row member index value found same
    have old : tree.nodeAt index = some value := by
      change actual.tree.nodes.get index = some value at found
      rw [congrArg BorrowTree.nodes shape] at found
      exact found
    exact hiddenFrame row member index value old same
  obtain ⟨finalRuntime,⟨finalPositive⟩⟩ := end_call actual.tree global frame afterRuntime afterHidden
    (some child) (some selected) maximum offset 1 afterPositive
  have afterPresent : actual.tree.nodeAt child = some node := by
    change actual.tree.nodes.get child = some node
    rw [congrArg BorrowTree.nodes shape]
    exact present
  have absent : (global.endCall frame).protectedTags.contains node.tag = false := by
    rw [sameTag]
    exact GeneralBorrowRelease.end_call_owned_absent global frame allocation tag owned
  exact ⟨done,finalRuntime,GeneralBorrowParentPositiveReanchor.positive actual.tree _ finalRuntime.formed.toGraphState
    child parent selected maximum offset 1 node afterPresent edge absent finalPositive,shape,capacity⟩

end DuplicatePrefix.S04ReturnReleaseParent
