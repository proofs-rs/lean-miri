import duplicate_prefix.S03EmptySharedGeometry
import duplicate_prefix.S03EmptyNextLenInput

namespace DuplicatePrefix.S03EmptyPositiveTreeFacts
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardParentTagOrder GeneralBorrowFreshRootSupportCutoff
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
attribute [local irreducible] UniValMap.insert
noncomputable section

variable {tree : BorrowTree} {global : GlobalState}
variable (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
variable (parentTag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag global.nextPointerTag)
variable (fresh : global.nextPointerTag.value < 18446744073709551615)
variable (room : tree.nodes.size+2 ≤ 4294967295)

abbrev next := S03EmptyNextLenInput.form tree global runtime parentTag input fresh room

theorem roots : (next runtime parentTag input fresh room).after.roots = tree.roots := by
  have first := GeneralBorrowFreshMetadata.roots input.stage input.after (GeneralBorrowSifaView.preserves input.stage input.parent .Read)
  let second := next runtime parentTag input fresh room
  have last := GeneralBorrowFreshMetadata.roots second.stage second.after (GeneralBorrowSifaView.preserves second.stage second.parent .Read)
  exact last.trans first

theorem capacity : (next runtime parentTag input fresh room).after.locations.size = tree.locations.size := by
  have first := GeneralBorrowFreshGeometry.shape_frame input.stage input.after
    (GeneralBorrowSifaView.preserves input.stage input.parent .Read) runtime.formed.well
  let second := next runtime parentTag input fresh room
  have last := GeneralBorrowFreshGeometry.shape_frame second.stage second.after
    (GeneralBorrowSifaView.preserves second.stage second.parent .Read) first.1
  exact last.2.trans first.2

theorem size : (next runtime parentTag input fresh room).after.nodes.size ≤ tree.nodes.size+2 := by
  let second := next runtime parentTag input fresh room
  have first := EmptyForestSharedPoolNext.node_size input
  have last := EmptyForestSharedPoolNext.node_size second
  have growth1 : EmptyForestSharedPoolNext.growth input ≤ 1 := by
    cases chosen : input.slot <;> simp only [EmptyForestSharedPoolNext.growth,chosen] <;> decide
  have growth2 : EmptyForestSharedPoolNext.growth second ≤ 1 := by
    cases chosen : second.slot <;> simp only [EmptyForestSharedPoolNext.growth,chosen] <;> decide
  change second.after.nodes.size ≤ tree.nodes.size+2
  omega

theorem tagged (oldTag : BorTag) (index : UniIndex) (known : tree.indexOfTag oldTag = some index) :
    (next runtime parentTag input fresh room).after.indexOfTag oldTag = some index :=
  S03EmptySharedFrame.tagged (next runtime parentTag input fresh room) oldTag index (S03EmptySharedFrame.tagged input oldTag index known)

theorem old_node (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node) :
    ∃ after, (next runtime parentTag input fresh room).after.nodeAt index = some after ∧
      after.tag = node.tag ∧ after.parent = node.parent ∧ after.isExposed = node.isExposed := by
  obtain ⟨middle,found,tag,parent,hidden⟩ := S03EmptySharedFrame.old_node input index node present
  obtain ⟨after,foundAfter,tagAfter,parentAfter,hiddenAfter⟩ :=
    S03EmptySharedFrame.old_node (next runtime parentTag input fresh room) index middle found
  exact ⟨after,foundAfter,tagAfter.trans tag,parentAfter.trans parent,hiddenAfter.trans hidden⟩

theorem hidden_frame (frame : FrameState) (hidden : S04ReturnReleaseParent.HiddenFrame tree frame) :
    S04ReturnReleaseParent.HiddenFrame (next runtime parentTag input fresh room).after frame :=
  S03EmptySharedGeometry.hidden_frame (next runtime parentTag input fresh room) frame (S03EmptySharedGeometry.hidden_frame input frame hidden)

theorem exposed (maximum : BorTag) (bound : ExposedBound tree maximum) :
    ExposedBound (next runtime parentTag input fresh room).after maximum :=
  S03EmptySharedGeometry.exposed (next runtime parentTag input fresh room) maximum (S03EmptySharedGeometry.exposed input maximum bound)

theorem order (ordered : ParentTagOrder tree) : ParentTagOrder (next runtime parentTag input fresh room).after := by
  let advanced := GeneralBorrowFnEntryRegistration.advanced global fresh
  have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag fresh
  have tagBound : global.nextPointerTag.value.toNat < advanced.nextPointerTag.value.toNat := by
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag fresh).value.toNat
    omega
  have raised : DuplicatePrefixBorrowContract.RuntimeFacts tree advanced :=
    ⟨runtime.formed,runtime.coherent,runtime.possible,
      GeneralBorrowForestTagHighWaterHistory.weaken tree global.protectedTags global.nextPointerTag advanced.nextPointerTag runtime.below (Nat.le_of_lt tagBound)⟩
  have firstRuntime := S03EmptySharedRuntime.construct tree advanced raised parentTag global.nextPointerTag input (by omega) tagBound
  exact S03EmptySharedGeometry.fresh_order input.after advanced firstRuntime global.nextPointerTag
    (next runtime parentTag input fresh room) (S03EmptySharedGeometry.fresh_order tree global runtime parentTag input ordered)

theorem old_leaf (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node)
    (different : index ≠ input.parent) (hidden : node.isExposed = false) (root : node.parent = none) (leaf : node.children = #[]) :
    ∃ after, (next runtime parentTag input fresh room).after.nodeAt index = some after ∧
      after.tag = node.tag ∧ after.isExposed = false ∧ after.parent = none ∧ after.children = #[] := by
  obtain ⟨middle,found,tag,hiddenMiddle,rootMiddle,leafMiddle⟩ := S03EmptySharedGeometry.old_leaf input index node present different hidden root leaf
  have nextParent : (next runtime parentTag input fresh room).parent = input.index := by rfl
  have nextDifferent : index ≠ (next runtime parentTag input fresh room).parent := by
    intro same
    rw [nextParent] at same
    rw [same] at present
    change tree.nodes.get input.index = some node at present
    rw [input.vacant] at present
    cases present
  obtain ⟨after,foundAfter,tagAfter,hiddenAfter,rootAfter,leafAfter⟩ :=
    S03EmptySharedGeometry.old_leaf (next runtime parentTag input fresh room) index middle found nextDifferent hiddenMiddle rootMiddle leafMiddle
  exact ⟨after,foundAfter,tagAfter.trans tag,hiddenAfter,rootAfter,leafAfter⟩

end
end DuplicatePrefix.S03EmptyPositiveTreeFacts
