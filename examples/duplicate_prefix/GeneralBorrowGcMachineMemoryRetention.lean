import duplicate_prefix.GeneralBorrowGcFrameProvenanceCollection
import duplicate_prefix.MemoryCopyBridge

namespace DuplicatePrefix.GeneralBorrowGcMachineMemoryRetention
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows ProvenanceGC
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The target remains an actual live-memory row, with its concrete source
node and coherent allocator. No successful collector outcome is required. -/
def Stored (memory : MemoryState Provenance BorrowTree K) (id : AllocId) (index : UniIndex) (tag : BorTag) : Prop :=
  ∃ allocation node, memory.live.find? (·.1 == id) = some (id,allocation) ∧
    allocation.allocation.extra.nodes.get index = some node ∧ node.tag = tag ∧
    GeneralBorrowGcAllocator.Invariant allocation.allocation.extra

def commit (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree) : MemoryState Provenance BorrowTree K :=
  {memory with live := (memory.live.filter (·.1 != id)).push (id,{entry with allocation:=entry.allocation.setExtra tree})}

theorem lookup_other (memory : MemoryState Provenance BorrowTree K) (target id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree) (different : target ≠ id) :
    (commit memory id entry tree).live.find? (·.1 == target) = memory.live.find? (·.1 == target) := by
  have predicates : (fun row : AllocId × LocalAllocation Provenance BorrowTree K => (row.1 != id) && (row.1 == target)) = (fun row => row.1 == target) := by
    funext row
    by_cases same : row.1 = target
    · simp [same,different]
    · simp [same]
  simp only [commit,Array.find?_push,Array.find?_filter]
  simp only [show (id == target) = false from by simp [Ne.symm different], Bool.false_eq_true, ↓reduceIte]
  simp only [Option.or_none]
  congr 1

theorem committed (memory : MemoryState Provenance BorrowTree K) (roots : Roots)
    (target : AllocId) (index : UniIndex) (tag : BorTag)
    (stored : Stored memory target index tag) (held : roots.tags.contains tag = true)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : memory.live.find? (·.1 == id) = some (id,entry)) :
    Stored (commit memory id entry (entry.allocation.extra.removeUnreachableTags roots.tags).tree) target index tag := by
  obtain ⟨allocation,node,found,nodePresent,tagged,allocator⟩ := stored
  by_cases same : target = id
  · subst id
    have equal : allocation=entry := congrArg Prod.snd (Option.some.inj (found.symm.trans present))
    subst allocation
    obtain ⟨next,nextPresent,nextTag⟩ := GeneralBorrowGcLiveRetained.collect entry.allocation.extra roots.tags index node nodePresent (tagged ▸ held)
    refine ⟨{entry with allocation:=entry.allocation.setExtra (entry.allocation.extra.removeUnreachableTags roots.tags).tree},next,?_,nextPresent,nextTag.trans tagged,?_⟩
    · exact MemoryCopyBridge.live_lookup_replaced memory target _
    · exact GeneralBorrowGcAllocatorFull.preserves _ _ allocator
  · exact ⟨allocation,node,(lookup_other memory target id entry _ same).trans found,nodePresent,tagged,allocator⟩

theorem mapped (memory : MemoryState Provenance BorrowTree K) (id : AllocId) (index : UniIndex) (tag : BorTag)
    (stored : Stored memory id index tag) :
    ∃ allocation node, memory.live.find? (·.1 == id) = some (id,allocation) ∧
      allocation.allocation.extra.nodes.get index = some node ∧ node.tag=tag ∧
      allocation.allocation.extra.tagMapping.get tag=some index := by
  obtain ⟨allocation,node,found,present,tagged,allocator⟩ := stored
  refine ⟨allocation,node,found,present,tagged,?_⟩
  simpa only [tagged] using allocator.nodeTags index node present

theorem final_prune (memory : MemoryState Provenance BorrowTree K) (roots : Roots)
    (id : AllocId) (index : UniIndex) (tag : BorTag) (stored : Stored memory id index tag) :
    Stored (memory.removeUnreachable roots.allocations) id index tag := stored
end DuplicatePrefix.GeneralBorrowGcMachineMemoryRetention
