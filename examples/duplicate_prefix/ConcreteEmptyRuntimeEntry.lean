import duplicate_prefix.ConcreteEmptyPoolEntryNext
import duplicate_prefix.DuplicatePrefixRuntimeInput
import duplicate_prefix.GeneralBorrowForestTagHighWater

namespace DuplicatePrefix.ConcreteEmptyRuntimeEntry
open Miri Miri.ABI Miri.Memory Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Static formed/SIFA data supplies depth, coherent pool/accounting and
vacant Clean for the actual append OR reuse branch. Parent presence, raw tag
freshness and explicit u32 capacity remain the caller conditions. Zero length
needs no byte ownership, initialization, or offset-containment premise. -/
def form (tree : BorrowTree) (protections : ProtectedTags) (parentTag tag : BorTag)
    (formed : GeneralBorrowStructuralHistorySifaState.Formed tree protections)
    (parent : UniIndex) (node : TreeNode) (tagged : tree.indexOfTag parentTag = some parent)
    (present : tree.nodeAt parent = some node) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size + 1 ≤ 4294967295) : ConcreteEmptyPoolEntry.Input tree parentTag tag := by
  have fits : tree.tagMapping.mapping.size ≤ 4294967295 := by
    have balance := formed.allocator.accounting
    unfold GeneralBorrowFreshStagePool.Accounting at balance
    omega
  exact ConcreteEmptyPoolEntry.factory tree parentTag tag parent node (Classical.choice formed.depth)
    tagged present fresh formed.allocator.pool formed.allocator.accounting fits
    (GeneralBorrowStructuralHistorySifaState.vacant_clean tree protections formed)

theorem counter_fresh (tree : BorrowTree) (global : GlobalState)
    (below : GeneralBorrowForestTagHighWater.Below tree global.protectedTags global.nextPointerTag) :
    GeneralBorrowTagMap.Fresh tree.tagMapping global.nextPointerTag := by
  intro row member same
  have less := below.mapping row member
  rw [same] at less
  omega

/-- Direct bridge from the live pre-call runtime record. No successful tag-map
insertion, constructor, release, history, or post-state fact is an input. -/
def from_runtime {K U : Type} (before : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (tracker : MachineHooks.BorrowState) (runtime : DuplicatePrefixRuntimeInput.State before tracker)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (live : before.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (parentTag : BorTag) (parent : UniIndex) (node : TreeNode)
    (tagged : entry.allocation.extra.indexOfTag parentTag = some parent)
    (present : entry.allocation.extra.nodeAt parent = some node)
    (below : GeneralBorrowForestTagHighWater.Below entry.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (room : entry.allocation.extra.nodes.size + 1 ≤ 4294967295) :
    ConcreteEmptyPoolEntry.Input entry.allocation.extra parentTag tracker.global.nextPointerTag :=
  form entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag
    (runtime.formed (id, entry) (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live)))
    parent node tagged present (counter_fresh entry.allocation.extra tracker.global below) room

/-- The actual zero protected Default constructor and lazy release complete,
and the residual arbitrary free pool, accounting and vacant Clean survive.
This is an operation theorem, not an all-count function theorem. -/
theorem construct (tree : BorrowTree) (protections : ProtectedTags) (parentTag tag : BorTag)
    (formed : GeneralBorrowStructuralHistorySifaState.Formed tree protections)
    (parent : UniIndex) (node : TreeNode) (tagged : tree.indexOfTag parentTag = some parent)
    (present : tree.nodeAt parent = some node) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (room : tree.nodes.size + 1 ≤ 4294967295) (offset : UInt64) :
    let input := form tree protections parentTag tag formed parent node tagged present fresh room
    tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true =
        ⟨input.after, .ok ()⟩ ∧
    input.after.releaseProtector tag protections = ⟨input.after, .Released⟩ ∧
    GeneralBorrowFreshAllocatorInvariant.Pool input.after.nodes input.after.tagMapping.deassigned ∧
    GeneralBorrowFreshStagePool.Accounting input.after ∧
    GeneralBorrowGcVacantClean.VacantClean input.after := by
  let input := form tree protections parentTag tag formed parent node tagged present fresh room
  have allocation := ConcreteEmptyPoolEntryNext.allocator input formed.allocator.pool formed.allocator.accounting
  exact ⟨input.child offset, input.release protections, allocation.1, allocation.2,
    ConcreteEmptyPoolEntryNext.vacant_clean input (GeneralBorrowStructuralHistorySifaState.vacant_clean tree protections formed)⟩

end
end DuplicatePrefix.ConcreteEmptyRuntimeEntry
