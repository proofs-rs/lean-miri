import duplicate_prefix.GeneralBorrowGcFrameProvenanceConditional
import duplicate_prefix.GeneralBorrowGcMachineMemoryRetentionRun

namespace DuplicatePrefix.GeneralBorrowGcFrameProvenanceMachineRetention
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows ProvenanceGC
open GeneralBorrowGcFrameProvenanceScalar GeneralBorrowGcFrameProvenanceVisitor GeneralBorrowGcFrameProvenanceStack
open GeneralBorrowGcMachineMemoryRetention GeneralBorrowGcMachineMemoryRetentionLoop
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- A concrete parent named by an actual live stack local survives the entire
actual machine provenance GC, including every error prefix. All source root
visitation and memory updates are evaluated by the fixed collector. There is
no collector-success, callback-success or supplied-live-tag premise. -/
theorem local_parent [DecidableEq K]
    (views : MachineGCRoots.Views User Os R Payload H D O)
    (addresses : FunctionPointers.AddressLens User AddressPayload)
    (state : MachineHooks.State K User)
    (frameIndex localId : Nat) (frame : ActualFrame) (entry : LocalState Provenance LocalLayout)
    (framePresent : state.stack.frames[frameIndex]? = some frame)
    (localPresent : frame.locals[localId]? = some entry)
    (id : AllocId) (allocation : LocalAllocation Provenance BorrowTree K)
    (allocationPresent : state.machine.memory.live.find? (·.1 == id) = some (id,allocation))
    (index : UniIndex) (node : TreeNode) (value : Immediate Provenance)
    (live : entry.value = .live (.immediate value))
    (pointer : GeneralBorrowGcFrameProvenanceScalar.Carries id node.tag value)
    (present : allocation.allocation.extra.nodes.get index = some node)
    (allocator : GeneralBorrowGcAllocator.Invariant allocation.allocation.extra) :
    Stored (stateOf (MachineGCRoots.run views addresses state)).machine.memory id index node.tag ∧
    ∃ finalAllocation finalNode,
      (stateOf (MachineGCRoots.run views addresses state)).machine.memory.live.find? (·.1 == id) = some (id,finalAllocation) ∧
      finalAllocation.allocation.extra.nodes.get index = some finalNode ∧ finalNode.tag = node.tag ∧
      finalAllocation.allocation.extra.tagMapping.get node.tag = some index := by
  have preserved : Stored (stateOf (MachineGCRoots.run views addresses state)).machine.memory id index node.tag := by
    apply GeneralBorrowGcMachineMemoryRetentionRun.run_preserves (MachineGCRoots.hooks views addresses)
      state id index node.tag ⟨allocation,node,allocationPresent,present,rfl,allocator⟩
    intro collected roots initial visited
    exact (GeneralBorrowGcFrameProvenanceConditional.local_rootsHeld views state frameIndex localId
      frame entry framePresent localPresent id node.tag value live pointer collected roots initial visited).1
  exact ⟨preserved,mapped _ id index node.tag preserved⟩

/-- The same real machine GC guarantee follows from an actual frame-owned
protected tag. The source node remains physical and maps to its original
sparse index even if a later allocation's GC reports an error. -/
theorem protected_parent [DecidableEq K]
    (views : MachineGCRoots.Views User Os R Payload H D O)
    (addresses : FunctionPointers.AddressLens User AddressPayload)
    (state : MachineHooks.State K User) (raw : StackForm state.stack)
    (frameIndex : Nat) (frame : ActualFrame) (borrow : FrameState)
    (framePresent : state.stack.frames[frameIndex]? = some frame)
    (borrowPresent : frame.extra.borrowTracker = some borrow)
    (id : AllocId) (allocation : LocalAllocation Provenance BorrowTree K)
    (allocationPresent : state.machine.memory.live.find? (·.1 == id) = some (id,allocation))
    (index : UniIndex) (node : TreeNode) (stored : (id,node.tag) ∈ borrow.protectedTags)
    (present : allocation.allocation.extra.nodes.get index = some node)
    (allocator : GeneralBorrowGcAllocator.Invariant allocation.allocation.extra) :
    Stored (stateOf (MachineGCRoots.run views addresses state)).machine.memory id index node.tag ∧
    ∃ finalAllocation finalNode,
      (stateOf (MachineGCRoots.run views addresses state)).machine.memory.live.find? (·.1 == id) = some (id,finalAllocation) ∧
      finalAllocation.allocation.extra.nodes.get index = some finalNode ∧ finalNode.tag = node.tag ∧
      finalAllocation.allocation.extra.tagMapping.get node.tag = some index := by
  have preserved : Stored (stateOf (MachineGCRoots.run views addresses state)).machine.memory id index node.tag := by
    apply GeneralBorrowGcMachineMemoryRetentionRun.run_preserves (MachineGCRoots.hooks views addresses)
      state id index node.tag ⟨allocation,node,allocationPresent,present,rfl,allocator⟩
    intro collected roots initial visited
    exact (GeneralBorrowGcFrameProvenanceMachineRoots.protector_rootsHeld views state raw frameIndex
      frame borrow framePresent borrowPresent id node.tag stored collected roots initial visited).1
  exact ⟨preserved,mapped _ id index node.tag preserved⟩

end DuplicatePrefix.GeneralBorrowGcFrameProvenanceMachineRetention
