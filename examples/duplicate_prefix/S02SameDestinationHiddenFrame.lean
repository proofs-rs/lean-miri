import duplicate_prefix.S04ReturnReleaseParent

namespace DuplicatePrefix.S02SameDestinationHiddenFrame
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Both owned tags name hidden nodes in the same current allocation. -/
theorem of_hidden (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (sourceId returnId : AllocId) (sourceTag returnTag : BorTag)
    (child : UniIndex) (node : TreeNode)
    (owned : frame.protectedTags = #[(sourceId,sourceTag),(returnId,returnTag)])
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (sourceChild : UniIndex) (sourceNode : TreeNode)
    (sourceTagged : tree.indexOfTag sourceTag = some sourceChild)
    (sourcePresent : tree.nodeAt sourceChild = some sourceNode)
    (sourceHidden : sourceNode.isExposed = false)
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
    have equal : query=sourceChild := Option.some.inj (mapped.symm.trans sourceTagged)
    subst query
    have same : value=sourceNode := Option.some.inj (found.symm.trans sourcePresent)
    exact same ▸ sourceHidden
  · subst row
    have mapped := runtime.formed.allocator.nodeTags query value found
    rw [sameTag] at mapped
    have equal : query=child := Option.some.inj (mapped.symm.trans returnTagged)
    subst query
    have same : value=node := Option.some.inj (found.symm.trans returnPresent)
    exact same ▸ returnHidden

end DuplicatePrefix.S02SameDestinationHiddenFrame

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationHiddenFrame.of_hidden) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination hidden-frame dependency {dependency}"
