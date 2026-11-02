import duplicate_prefix.GeneralBorrowGcFrameProvenanceRetained

namespace DuplicatePrefix.GeneralBorrowGcFrameProvenanceCollection
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows ProvenanceGC
open GeneralBorrowGcFrameProvenanceScalar GeneralBorrowGcFrameProvenanceVisitor GeneralBorrowGcFrameProvenanceStack
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Exact allocation scan preceding the active-stack visitor in production
`ProvenanceGC.run`. The seed is computed from actual live allocation storage,
not supplied as an additional-live-tag contract. -/
def allocationRoots (state : MachineHooks.State K User) : Roots := Id.run do
  let mut roots : Roots := {}
  for (_,entry) in state.machine.memory.live do
    roots := roots.allocation state.machine.borrowTracker.isSome entry.allocation
  return roots

/-- The actual first two source collection stages. User-embedded root scanning
and the whole-machine pruning loop are subsequent stages. -/
def collect (state : MachineHooks.State K User) : Except StepError Roots :=
  (allocationRoots state).stack state.stack

/-- A raw pointer in a real machine frame/local reaches the actual allocation
and stack collection array and therefore prevents its concrete parent from
becoming missing when that array drives the production tree collector. -/
theorem local_pointer (state : MachineHooks.State K User) (tree : BorrowTree)
    (raw : StackForm state.stack) (frameIndex localId : Nat) (frame : ActualFrame)
    (entry : LocalState Provenance LocalLayout)
    (framePresent : state.stack.frames[frameIndex]? = some frame)
    (localPresent : frame.locals[localId]? = some entry)
    (id : AllocId) (index : UniIndex) (node : TreeNode) (value : Immediate Provenance)
    (live : entry.value = .live (.immediate value))
    (pointer : GeneralBorrowGcFrameProvenanceScalar.Carries id node.tag value)
    (present : tree.nodes.get index = some node)
    (allocator : GeneralBorrowGcAllocator.Invariant tree) :
    ∃ collected, collect state = .ok collected ∧ collected.tags.contains node.tag = true ∧
      collected.allocations.contains id = true ∧
      ∃ next, (tree.removeUnreachableTags collected.tags).tree.nodes.get index = some next ∧
        next.tag = node.tag ∧ (tree.removeUnreachableTags collected.tags).tree.tagMapping.get node.tag = some index :=
  GeneralBorrowGcFrameProvenanceRetained.local_pointer tree (allocationRoots state) state.stack raw
    frameIndex localId frame entry framePresent localPresent id index node value live pointer present allocator

/-- Frame-owned protectors are collected by those same source stages. -/
theorem protector (state : MachineHooks.State K User) (tree : BorrowTree)
    (raw : StackForm state.stack) (frameIndex : Nat) (frame : ActualFrame) (borrow : FrameState)
    (framePresent : state.stack.frames[frameIndex]? = some frame)
    (borrowPresent : frame.extra.borrowTracker = some borrow)
    (id : AllocId) (index : UniIndex) (node : TreeNode)
    (stored : (id,node.tag) ∈ borrow.protectedTags)
    (present : tree.nodes.get index = some node)
    (allocator : GeneralBorrowGcAllocator.Invariant tree) :
    ∃ collected, collect state = .ok collected ∧ collected.tags.contains node.tag = true ∧
      collected.allocations.contains id = true ∧
      ∃ next, (tree.removeUnreachableTags collected.tags).tree.nodes.get index = some next ∧
        next.tag = node.tag ∧ (tree.removeUnreachableTags collected.tags).tree.tagMapping.get node.tag = some index :=
  GeneralBorrowGcFrameProvenanceRetained.protector tree (allocationRoots state) state.stack raw
    frameIndex frame borrow framePresent borrowPresent id index node stored present allocator

/-- The source node belongs to the same live allocation named by the concrete
stack pointer; both the allocation lookup and local lookup are raw storage
facts. Collection and retention are derived, rather than assumed outcomes. -/
theorem live_parent (state : MachineHooks.State K User)
    (raw : StackForm state.stack) (frameIndex localId : Nat) (frame : ActualFrame)
    (entry : LocalState Provenance LocalLayout)
    (framePresent : state.stack.frames[frameIndex]? = some frame)
    (localPresent : frame.locals[localId]? = some entry)
    (id : AllocId) (allocation : LocalAllocation Provenance BorrowTree K)
    (allocationPresent : state.machine.memory.live.find? (·.1 == id) = some (id,allocation))
    (index : UniIndex) (node : TreeNode) (value : Immediate Provenance)
    (live : entry.value = .live (.immediate value))
    (pointer : GeneralBorrowGcFrameProvenanceScalar.Carries id node.tag value)
    (present : allocation.allocation.extra.nodes.get index = some node)
    (allocator : GeneralBorrowGcAllocator.Invariant allocation.allocation.extra) :
    ∃ collected, collect state = .ok collected ∧ collected.tags.contains node.tag = true ∧
      collected.allocations.contains id = true ∧
      state.machine.memory.live.find? (·.1 == id) = some (id,allocation) ∧
      ∃ next, (allocation.allocation.extra.removeUnreachableTags collected.tags).tree.nodes.get index = some next ∧
        next.tag = node.tag ∧ (allocation.allocation.extra.removeUnreachableTags collected.tags).tree.tagMapping.get node.tag = some index := by
  obtain ⟨collected,done,held,idHeld,nodeHeld⟩ := local_pointer state allocation.allocation.extra raw
    frameIndex localId frame entry framePresent localPresent id index node value live pointer present allocator
  exact ⟨collected,done,held,idHeld,allocationPresent,nodeHeld⟩

end DuplicatePrefix.GeneralBorrowGcFrameProvenanceCollection
