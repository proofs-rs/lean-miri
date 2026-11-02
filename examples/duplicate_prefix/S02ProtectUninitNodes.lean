import duplicate_prefix.S02FnEntryFreshNode
import duplicate_prefix.S02FnEntryOldNode
import duplicate_prefix.S02FnEntryBinding
import duplicate_prefix.GeneralBorrowFreshReadFrame

namespace DuplicatePrefix.S02ProtectUninitNodes
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- The literal uninit Write leaves all FnEntry node and tag metadata exact,
independently of the ranged access outcome. -/
theorem frame (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global) :
    let retagged := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let global := TypedRetagGeneric.protectedGlobal tracker.global input.tagRoom
    let written := (retagged.performBorrowAccessRange (.concrete tracker.global.nextPointerTag)
      (Size.ofBytes input.offset) (Size.ofBytes input.len) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    written.nodes = retagged.nodes ∧ written.tagMapping = retagged.tagMapping := by
  dsimp only
  have framed := GeneralBorrowFreshReadFrame.frame
    (GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len)
    (.concrete tracker.global.nextPointerTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Write (TypedRetagGeneric.protectedGlobal tracker.global input.tagRoom).protectedTags .VisitChildrenOfAccessed
  have nodes := congrArg BorrowTree.nodes framed
  have tags := congrArg BorrowTree.tagMapping framed
  exact ⟨nodes,tags⟩

/-- Every existing source node keeps its tag and exposure through real return
FnEntry and the literal uninit Write in that same allocation. -/
theorem old_node (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node)
    (tag : BorTag) (tagged : tree.indexOfTag tag = some query) :
    let retagged := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let global := TypedRetagGeneric.protectedGlobal tracker.global input.tagRoom
    let written := (retagged.performBorrowAccessRange (.concrete tracker.global.nextPointerTag)
      (Size.ofBytes input.offset) (Size.ofBytes input.len) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    written.indexOfTag tag = some query ∧ ∃ next,written.nodeAt query = some next ∧ next.tag = node.tag ∧ next.isExposed = node.isExposed := by
  obtain ⟨next,lookup,same,hidden⟩ := S02FnEntryOldNode.preserved tree tracker borrowFrame allocation runtime input query node present
  have mapped := S02FnEntryBinding.mapped tree tracker borrowFrame allocation runtime input tag query tagged
  have framed := frame tree tracker input
  refine ⟨?_,next,?_,same,hidden⟩
  · unfold BorrowTree.indexOfTag
    rw [framed.2]
    exact mapped
  · unfold BorrowTree.nodeAt
    rw [framed.1]
    exact lookup

/-- The real return child remains a fresh hidden leaf with its exact parent
through the literal uninit Write. -/
theorem new_node (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global) :
    let retagged := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let global := TypedRetagGeneric.protectedGlobal tracker.global input.tagRoom
    let written := (retagged.performBorrowAccessRange (.concrete tracker.global.nextPointerTag)
      (Size.ofBytes input.offset) (Size.ofBytes input.len) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    ∃ child node,written.indexOfTag tracker.global.nextPointerTag = some child ∧ written.nodeAt child = some node ∧
      node.tag = tracker.global.nextPointerTag ∧ node.parent = some input.parent ∧ node.children = #[] ∧ node.isExposed = false := by
  obtain ⟨child,node,tagged,present,same,parent,leaf,hidden⟩ := S02FnEntryFreshNode.node tree tracker borrowFrame allocation runtime input
  have framed := frame tree tracker input
  refine ⟨child,node,?_,?_,same,parent,leaf,hidden⟩
  · unfold BorrowTree.indexOfTag
    rw [framed.2]
    exact tagged
  · unfold BorrowTree.nodeAt
    rw [framed.1]
    exact present

end DuplicatePrefix.S02ProtectUninitNodes

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02ProtectUninitNodes.old_node,``DuplicatePrefix.S02ProtectUninitNodes.new_node] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
