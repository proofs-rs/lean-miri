import duplicate_prefix.GeneralBorrowRawTargetActivity
import duplicate_prefix.S02SameDestinationRejectedResultActivity
import duplicate_prefix.GeneralBorrowFreshResult
import duplicate_prefix.GeneralBorrowFreshReuseChild
import duplicate_prefix.GeneralBorrowFreshActiveWithinModify
namespace DuplicatePrefix.S02SameDestinationAcceptedHelperActivity
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshChild DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralBorrowFreshMaterialization DuplicatePrefix.GeneralBorrowFreshActiveWithin
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

private theorem modified_sifa (tree : BorrowTree) (index parent target : UniIndex)
    (offset len : Size) (lower upper : UInt64)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (different : target ≠ index)
    (active : ActiveWithin tree target .Write lower upper) :
    ActiveWithin
      (sourceUpdateSifa {tree with locations := (tree.locations.modifyRange offset len
        (fun _ location => materialized location index inside)).state} parent .None).1 target .Write lower upper := by
  have updated := S02SameDestinationRejectedResultActivity.modified tree.locations target offset len
    (fun _ location => materialized location index inside) lower upper well bounds (by
      intro range location
      exact GeneralBorrowFreshLocation.get_other location.perms index target inside different) active
  exact sifa_preserves
    {tree with locations := (tree.locations.modifyRange offset len
      (fun _ location => materialized location index inside)).state} parent .None target .Write lower upper updated

set_option autoImplicit false in
/-- A real mutable append preserves an older anchor's strong Write activity.
This is a data-preservation statement, not a claim that an arbitrary access succeeds. -/
theorem append (tree : BorrowTree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (noFree : tree.tagMapping.deassigned.back? = none) (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (target : UniIndex) (lower upper : UInt64)
    (targetNode : TreeNode) (targetPresent : tree.nodeAt target = some targetNode)
    (active : ActiveWithin tree target .Write lower upper) :
    ActiveWithin (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) true).tree target .Write lower upper := by
  rw [GeneralBorrowFreshResult.mutable_tree tree parentTag newTag parent parentNode parentTagPresent parentPresent
    fresh noFree aligned fits offset len nonzero well bounds]
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let base : BorrowTree := {(GeneralBorrowFreshGraph.attached tree index parent parentNode (child newTag parent)) with
    tagMapping := ⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned⟩}
  have wellBase : base.locations.WellFormed := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact well
  have boundsBase : offset.toNat+len.toNat ≤ base.locations.size.bytes.toNat := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact bounds
  have activeBase : ActiveWithin base target .Write lower upper := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact active
  have different : target ≠ index := by
    intro equal
    have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes target targetNode targetPresent
    have atEnd : index.toNat = tree.nodes.data.size := by
      dsimp only [index,UniIndex.toNat]
      rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega)]
      exact aligned
    rw [equal,atEnd] at valid
    omega
  have saved := modified_sifa base index parent target (Size.ofBytes offset) (Size.ofBytes len) lower upper
    wellBase boundsBase different activeBase
  simpa only [base,index,materialized,GeneralBorrowFreshGraph.attached,Size.ofBytes] using saved

set_option autoImplicit false in
/-- Reusing a vacant slot likewise preserves the older anchor's strong profile. -/
theorem reuse (tree : BorrowTree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (index : UniIndex) (available : tree.tagMapping.deassigned.back? = some index)
    (indexBound : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (target : UniIndex) (lower upper : UInt64)
    (targetNode : TreeNode) (targetPresent : tree.nodeAt target = some targetNode)
    (active : ActiveWithin tree target .Write lower upper) :
    ActiveWithin (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) true).tree target .Write lower upper := by
  have different : target ≠ index := by
    intro equal
    change tree.nodes.get target = some targetNode at targetPresent
    rw [equal,vacant] at targetPresent
    cases targetPresent
  have returned : (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) true).tree =
      (sourceUpdateSifa
        {(GeneralBorrowFreshGraph.attached tree index parent parentNode (child newTag parent)) with
          tagMapping := ⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned.pop⟩
          locations := (tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
            (fun _ location => materialized location index inside)).state} parent .None).1 := by
    simpa only [GeneralBorrowFreshGraph.attached,materialized] using GeneralBorrowFreshReuseChild.mutable_tree tree
      parentTag newTag parent parentNode parentTagPresent parentPresent fresh index available indexBound vacant offset len nonzero well bounds
  rw [returned]
  let base : BorrowTree := {(GeneralBorrowFreshGraph.attached tree index parent parentNode (child newTag parent)) with
    tagMapping := ⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned.pop⟩}
  have wellBase : base.locations.WellFormed := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact well
  have boundsBase : offset.toNat+len.toNat ≤ base.locations.size.bytes.toNat := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact bounds
  have activeBase : ActiveWithin base target .Write lower upper := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact active
  have saved := modified_sifa base index parent target (Size.ofBytes offset) (Size.ofBytes len) lower upper
    wellBase boundsBase different activeBase
  simpa only [base,materialized,GeneralBorrowFreshGraph.attached,Size.ofBytes] using saved
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (target : UniIndex) (lower upper : UInt64)
    (targetNode : TreeNode) (targetPresent : tree.nodeAt target = some targetNode)
    (active : ActiveWithin tree target .Write lower upper) :
    ActiveWithin (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree target .Write lower upper := by
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    exact S02SameDestinationAcceptedHelperActivity.append tree parentTag newTag parent parentNode tagged present fresh
      noFree aligned fits offset len nonzero runtime.formed.well bounds target lower upper targetNode targetPresent active
  | reuse child available valid vacant slack =>
    exact S02SameDestinationAcceptedHelperActivity.reuse tree parentTag newTag parent parentNode tagged present fresh
      child available valid vacant offset len nonzero runtime.formed.well bounds target lower upper targetNode targetPresent active

end DuplicatePrefix.S02SameDestinationAcceptedHelperActivity
