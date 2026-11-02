import duplicate_prefix.S02SameDestinationRejectedResultReadReleaseScan
namespace DuplicatePrefix.S02SameDestinationRejectedResultReadRelease
open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- A real authorized hidden-source release preserves a distinct hidden leaf's
bytewise activity window, including arbitrary physical-root callbacks. -/
theorem release (tree : BorrowTree) (global : GlobalState)
    (before : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (tag : BorTag) (anchor selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (positive : GeneralBorrowReadRowRange.Positive tree global.protectedTags anchor selected maximum offset len)
    (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode) (hidden : anchorNode.isExposed = false)
    (tagged : tree.indexOfTag tag = some anchor) (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Read offset (offset+len))
    (target : UniIndex) (targetNode : TreeNode) (targetPresent : tree.nodeAt target = some targetNode)
    (targetLeaf : targetNode.children = #[]) (targetHidden : targetNode.isExposed = false)
    (different : target ≠ anchor) (targetLower targetUpper : UInt64)
    (targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write targetLower targetUpper) :
    GeneralBorrowFreshActiveWithin.ActiveWithin
      (tree.releaseProtector tag global.protectedTags).tree target .Write targetLower targetUpper := by
  have fits : offset.toNat+len.toNat < 2^64 := Nat.lt_of_le_of_lt positive.bounds tree.locations.size.bytes.toNat_lt
  have sum : (offset+len).toNat = offset.toNat+len.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
  have nonempty : offset.toNat < (offset+len).toNat := by rw [sum];have p:=positive.positive;omega
  have runtime : Every (GeneralBorrowSnapshotWildcardRangeBoth.Runtime tree global.protectedTags) tree.locations := by
    intro position valid
    exact ⟨before.coherent position valid,before.formed.profile position valid,before.possible position valid⟩
  obtain ⟨_,_,_,_,_,_,_,activity⟩ := S02SameDestinationRejectedResultReadReleaseScan.release tree global.protectedTags
    tag anchor selected maximum offset (offset+len) nonempty before.formed.toGraphState anchorNode present hidden distinct order short
    tagged active before.formed.well runtime positive.rows target targetNode targetPresent targetLeaf targetHidden different
    targetLower targetUpper targetActive
  exact activity
end DuplicatePrefix.S02SameDestinationRejectedResultReadRelease

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationRejectedResultReadRelease.release) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved hidden leaf active release dependency {dependency}"
