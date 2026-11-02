import duplicate_prefix.S04ReturnReleaseParent

namespace DuplicatePrefix.S02SeparateDestinationHiddenFrame
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The owned source tag is absent from the distinct destination tree, while
its only owned destination tag belongs to the hidden return child. -/
theorem of_absent (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (sourceId returnId : AllocId) (sourceTag returnTag : BorTag)
    (child : UniIndex) (node : TreeNode)
    (owned : frame.protectedTags = #[(sourceId,sourceTag),(returnId,returnTag)])
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (sourceAbsent : tree.indexOfTag sourceTag = none)
    (returnTagged : tree.indexOfTag returnTag = some child)
    (returnPresent : tree.nodeAt child = some node)
    (returnHidden : node.isExposed = false) :
    S04ReturnReleaseParent.HiddenFrame tree frame := by
  intro row member query value found sameTag
  have rows : row=(sourceId,sourceTag) ∨ row=(returnId,returnTag) := by
    simpa [owned] using member
  rcases rows with equal | equal
  · subst row
    have mapped := runtime.formed.allocator.nodeTags query value found
    rw [sameTag] at mapped
    change tree.indexOfTag sourceTag = some query at mapped
    rw [sourceAbsent] at mapped
    cases mapped
  · subst row
    have mapped := runtime.formed.allocator.nodeTags query value found
    rw [sameTag] at mapped
    have equal : query=child := Option.some.inj (mapped.symm.trans returnTagged)
    subst query
    have same : value=node := Option.some.inj (found.symm.trans returnPresent)
    exact same ▸ returnHidden

end DuplicatePrefix.S02SeparateDestinationHiddenFrame

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationHiddenFrame.of_absent) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination hidden-frame dependency {dependency}"
