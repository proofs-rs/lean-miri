import duplicate_prefix.S04ProtectUninit
import duplicate_prefix.GlobalAddressLiveErrorExclusion

namespace DuplicatePrefix.S03WildcardMissLookupFrame
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Replacing a live allocation without changing its size preserves exactly
the size/liveness hooks used by wildcard resolution, even when bytes,
initialization, provenance and Tree Borrows state change. -/
theorem lookup_updated {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (updated : Allocation Provenance BorrowTree)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : updated.byteSize = entry.allocation.byteSize) :
    GlobalAddressLiveErrorExclusion.lookup
      {memory with live := (memory.live.filter fun row => row.1 != id).push (id,{entry with allocation := updated})} =
      GlobalAddressLiveErrorExclusion.lookup memory := by
  let after : MemoryState Provenance BorrowTree K :=
    {memory with live := (memory.live.filter fun row => row.1 != id).push (id,{entry with allocation := updated})}
  have other (query : AllocId) (different : query ≠ id) :
      after.live.find? (fun row => row.1 == query) = memory.live.find? (fun row => row.1 == query) := by
    have filtered : (memory.live.filter (fun row => row.1 != id)).find? (fun row => row.1 == query) =
        memory.live.find? (fun row => row.1 == query) := by
      rw [Array.find?_filter]
      congr 1
      funext row
      by_cases eqQuery : (row.1 == query) = true
      · have equal : row.1 = query := beq_iff_eq.mp eqQuery
        have neId : row.1 ≠ id := fun h => different (equal.symm.trans h)
        have keep : (row.1 != id) = true := by simpa using neId
        simp [eqQuery,keep]
      · simp [eqQuery]
    simp [after,Array.find?_push,Ne.symm different,filtered]
  have sizes (query : AllocId) :
      (after.getAllocInfo query).toOption.map AllocationInfo.size =
        (memory.getAllocInfo query).toOption.map AllocationInfo.size := by
    by_cases same : query = id
    · subst query
      have next := MemoryCopyBridge.live_lookup_replaced memory id {entry with allocation := updated}
      change after.live.find? (fun row => row.1 == id) = some (id,{entry with allocation := updated}) at next
      simp only [MemoryState.getAllocInfo,next,present,Except.toOption,Option.map_some,size]
      rfl
    · unfold MemoryState.getAllocInfo
      rw [other query same]
      rfl
  have live (query : AllocId) : after.isAllocLive query = memory.isAllocLive query := by
    by_cases same : query = id
    · subst query
      have prior := MemoryCopyBridge.live_any_of_present memory id entry present
      have next := MemoryCopyBridge.live_any_replaced memory id {entry with allocation := updated}
      simp only [after,MemoryState.isAllocLive,prior,next,Bool.true_or]
    · have predicates : (fun row : AllocId × LocalAllocation Provenance BorrowTree K => (row.1 != id) && (row.1 == query)) =
          (fun row => row.1 == query) := by
        funext row
        by_cases equal : row.1 = query
        · simp [equal,same]
        · simp [equal]
      simp only [after,MemoryState.isAllocLive,Array.any_push,Array.any_filter,predicates,
        show (id == query) = false from by simpa using Ne.symm same,Bool.or_false]
  unfold GlobalAddressLiveErrorExclusion.lookup
  congr 1
  · funext query
    exact sizes query
  · funext query
    exact congrArg some (live query)

/-- Exact hook preservation on the actual protection/uninit machine, including
its two source-order updates of the same live allocation. -/
theorem lookup_finished {before : DuplicatePrefixCallSpecification.Before} {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (size : updated.byteSize = input.entry.allocation.byteSize) :
    GlobalAddressLiveErrorExclusion.lookup
      (S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated).machine.memory =
      GlobalAddressLiveErrorExclusion.lookup before.memory := by
  have twice := MemoryCopyBridge.live_update_twice before.memory input.id
    {input.entry with allocation := input.entry.allocation.setExtra tree} {input.entry with allocation := updated}
  have memory : (S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated).machine.memory =
      {before.memory with live := ((before.memory.live.filter (fun row => row.1 != input.id)).push
        (input.id,{input.entry with allocation := updated}))} := twice
  rw [memory]
  exact lookup_updated before.memory input.id input.entry updated input.live size

end DuplicatePrefix.S03WildcardMissLookupFrame
