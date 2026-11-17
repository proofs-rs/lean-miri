import duplicate_prefix.GeneralBorrowReadProtectorReleaseScan
namespace DuplicatePrefix.GeneralBorrowReadProtectorRelease
open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralBorrowReadRowRange
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Full actual unexposed Read-helper release, with arbitrary roots, initial
outside-source activity, allocator pools and exposed caches. The fresh child's
own activity window bounds the real scan's accessed rows. -/
theorem release (tree : BorrowTree) (global : GlobalState)
    (before : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (anchor selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (positive : Positive tree global.protectedTags anchor selected maximum offset len)
    (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode) (hidden : anchorNode.isExposed = false)
    (tagged : tree.indexOfTag tag = some anchor) (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Read offset (offset+len)) :
    let actual := tree.releaseProtector tag global.protectedTags
    actual.status = .Released ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
    Nonempty (Positive actual.tree global.protectedTags anchor selected maximum offset len) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin actual.tree anchor .Write offset (offset+len) ∧
    actual.tree = {tree with locations := actual.tree.locations} ∧ actual.tree.locations.size = tree.locations.size := by
  have fits : offset.toNat+len.toNat < 2^64 := Nat.lt_of_le_of_lt positive.bounds tree.locations.size.bytes.toNat_lt
  have sum : (offset+len).toNat = offset.toNat+len.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  have nonempty : offset.toNat < (offset+len).toNat := by rw [sum];have p:=positive.positive;omega
  have runtime : Every (GeneralBorrowSnapshotWildcardRangeBoth.Runtime tree global.protectedTags) tree.locations := by
    intro position valid
    exact ⟨before.coherent position valid,before.formed.profile position valid,before.possible position valid⟩
  obtain ⟨done,frame,rows,allRuntime,activity,well,capacity⟩ := GeneralBorrowReadProtectorReleaseScan.release tree global.protectedTags
    tag anchor selected maximum offset (offset+len) nonempty before.formed.toGraphState anchorNode present hidden distinct order short
    tagged active before.formed.well runtime positive.rows
  let actual := tree.releaseProtector tag global.protectedTags
  have graph := GeneralBorrowStructuralHistoryState.graph_locations tree actual.tree.locations before.formed.toGraphState
  rw [←frame] at graph
  have finalRuntime : DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global := by
    refine ⟨⟨⟨graph,well⟩,?_⟩,?_,?_,?_⟩
    · intro position valid;exact (allRuntime position valid).profile
    · intro position valid;exact (allRuntime position valid).coherent
    · intro position valid;exact (allRuntime position valid).possible
    · have tags := congrArg BorrowTree.tagMapping frame
      refine ⟨?_,before.below.protectors⟩
      rw [tags]
      exact before.below.mapping
  refine ⟨done,finalRuntime,⟨⟨positive.positive,?_,?_,rows⟩⟩,activity,frame,capacity⟩
  · rw [capacity];exact positive.bounds
  · refine ⟨anchorNode,?_⟩
    have nodes := congrArg BorrowTree.nodes frame
    change actual.tree.nodes.get anchor = some anchorNode
    rw [nodes]
    exact present
end DuplicatePrefix.GeneralBorrowReadProtectorRelease
