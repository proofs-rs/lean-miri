import duplicate_prefix.EmptyForestSharedReleaseFrame
import duplicate_prefix.ActualWildcardHitReference

namespace DuplicatePrefix.EmptyForestSharedReleaseData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshNode
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Initial structural and vacant-permission data for a zero-length reference.
This contains no operation-success or release equation. -/
structure Data (tree : BorrowTree) (tag : BorTag) where
  index : UniIndex
  node : TreeNode
  tagged : tree.indexOfTag tag = some index
  present : tree.nodeAt index = some node
  unexposed : node.isExposed = false
  absent : ∀ position (valid : position < tree.locations.entries.size),
    tree.locations.entries[position].data.perms.get index = none

/-- Real wildcard HIT insertion forms the original ROOT's release data directly
from the initial allocation and the vacant permission at its appended index. -/
def wildcard (tree : BorrowTree) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (clean : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ = none) :
    Data (ActualWildcardHitReference.finalTree tree tag) tag := by
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  have atEnd : index.toNat = tree.nodes.data.size := by
    simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
    exact aligned
  exact ⟨index,WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None,
    GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag fresh index tree.tagMapping.deassigned,
    append_get_same tree.nodes index _ atEnd,rfl,clean⟩

/-- Preserve the original zero reference's release data through each actual
zero shared append, even if the appended reference chooses it as parent. -/
noncomputable def after {tree : BorrowTree} {rootTag parentTag newTag : BorTag}
    (input : EmptyForestSharedAppend.Input tree parentTag newTag) (old : Data tree rootTag) :
    Data input.after rootTag := by
  let witness := EmptyForestSharedReleaseFrame.old_node input old.index old.node old.present
  let node := Classical.choose witness
  have present := (Classical.choose_spec witness).1
  have flag := (Classical.choose_spec witness).2
  have different : newTag ≠ rootTag := by
    intro equal
    subst rootTag
    have contradiction := old.tagged
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,
      GeneralBorrowTagMap.fresh_find tree.tagMapping newTag input.fresh,Option.map_none] at contradiction
    cases contradiction
  refine ⟨old.index,node,?_,present,flag.trans old.unexposed,
    EmptyForestSharedAppendNext.future_clean input old.index old.absent⟩
  unfold BorrowTree.indexOfTag
  rw [EmptyForestSharedAppendNext.mapping input]
  exact (GeneralBorrowTagMap.pushed_get_old tree.tagMapping newTag rootTag different input.index tree.tagMapping.deassigned).trans old.tagged

end DuplicatePrefix.EmptyForestSharedReleaseData
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.EmptyForestSharedReleaseData." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty release data {dependency}"
