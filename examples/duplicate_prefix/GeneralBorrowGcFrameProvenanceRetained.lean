import duplicate_prefix.GeneralBorrowGcFrameProvenanceStack
import duplicate_prefix.GeneralBorrowGcLiveRetained
import duplicate_prefix.GeneralBorrowGcAllocatorFull

namespace DuplicatePrefix.GeneralBorrowGcFrameProvenanceRetained
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows ProvenanceGC
open GeneralBorrowGcFrameProvenanceScalar GeneralBorrowGcFrameProvenanceVisitor GeneralBorrowGcFrameProvenanceStack
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The production tree collector cannot delete a concrete parent whose tag
was collected from actual stack storage. This also covers collector error
prefixes: no successful GC outcome is assumed. -/
theorem retained (tree : BorrowTree) (roots : Roots) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node)
    (held : roots.tags.contains node.tag = true)
    (allocator : GeneralBorrowGcAllocator.Invariant tree) :
    ∃ next, (tree.removeUnreachableTags roots.tags).tree.nodes.get index = some next ∧
      next.tag = node.tag ∧ (tree.removeUnreachableTags roots.tags).tree.tagMapping.get node.tag = some index := by
  obtain ⟨next,found,same⟩ := GeneralBorrowGcLiveRetained.collect tree roots.tags index node present held
  refine ⟨next,found,same,?_⟩
  have coherent := (GeneralBorrowGcAllocatorFull.preserves tree roots.tags allocator).nodeTags index next found
  simpa only [same] using coherent

/-- Actual indexed live locals, including either scalar of a wide immediate,
produce a retained, mapped parent after production borrow-tree collection.
Raw representation fields derive the visitor outcome internally. -/
theorem local_pointer (tree : BorrowTree) (roots : Roots) (stack : ThreadStacks.ActualStack)
    (raw : StackForm stack) (frameIndex localId : Nat) (frame : ActualFrame)
    (entry : LocalState Provenance LocalLayout)
    (framePresent : stack.frames[frameIndex]? = some frame)
    (localPresent : frame.locals[localId]? = some entry)
    (id : AllocId) (index : UniIndex) (node : TreeNode) (value : Immediate Provenance)
    (live : entry.value = .live (.immediate value))
    (pointer : GeneralBorrowGcFrameProvenanceScalar.Carries id node.tag value)
    (present : tree.nodes.get index = some node)
    (allocator : GeneralBorrowGcAllocator.Invariant tree) :
    ∃ collected, roots.stack stack = .ok collected ∧ collected.tags.contains node.tag = true ∧
      collected.allocations.contains id = true ∧
      ∃ next, (tree.removeUnreachableTags collected.tags).tree.nodes.get index = some next ∧
        next.tag = node.tag ∧ (tree.removeUnreachableTags collected.tags).tree.tagMapping.get node.tag = some index := by
  obtain ⟨collected,done,_,held,allocation⟩ := GeneralBorrowGcFrameProvenanceStack.local_pointer roots stack raw
    frameIndex localId frame entry framePresent localPresent id node.tag value live pointer
  exact ⟨collected,done,held,allocation,retained tree collected index node present held allocator⟩

/-- An actual frame-owned protector is another concrete source of the same
retention guarantee, independent of global protector lookup. -/
theorem protector (tree : BorrowTree) (roots : Roots) (stack : ThreadStacks.ActualStack)
    (raw : StackForm stack) (frameIndex : Nat) (frame : ActualFrame) (borrow : FrameState)
    (framePresent : stack.frames[frameIndex]? = some frame)
    (borrowPresent : frame.extra.borrowTracker = some borrow)
    (id : AllocId) (index : UniIndex) (node : TreeNode)
    (stored : (id,node.tag) ∈ borrow.protectedTags)
    (present : tree.nodes.get index = some node)
    (allocator : GeneralBorrowGcAllocator.Invariant tree) :
    ∃ collected, roots.stack stack = .ok collected ∧ collected.tags.contains node.tag = true ∧
      collected.allocations.contains id = true ∧
      ∃ next, (tree.removeUnreachableTags collected.tags).tree.nodes.get index = some next ∧
        next.tag = node.tag ∧ (tree.removeUnreachableTags collected.tags).tree.tagMapping.get node.tag = some index := by
  obtain ⟨collected,done,_,held,allocation⟩ := GeneralBorrowGcFrameProvenanceStack.protector roots stack raw
    frameIndex frame borrow id node.tag framePresent borrowPresent stored
  exact ⟨collected,done,held,allocation,retained tree collected index node present held allocator⟩

end DuplicatePrefix.GeneralBorrowGcFrameProvenanceRetained
