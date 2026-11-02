import duplicate_prefix.GlobalAddressPhysicalRowHistory
namespace DuplicatePrefix.GlobalAddressLocalRowFormation
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def Row {K} (memory : MemoryState Provenance BorrowTree K) (id : AllocId) (size : Size) : Prop :=
  ∃entry,memory.live.find? (fun row=>row.1==id)=some (id,entry) ∧ size=entry.allocation.byteSize

def Rows {K} (memory : MemoryState Provenance BorrowTree K) (entries : Array InverseAddressEntry) (sizes : AllocId→Size) : Prop :=
  ∀row∈entries,Row memory row.allocId (sizes row.allocId)

theorem insert_other {K} (memory : MemoryState Provenance BorrowTree K) (id query : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (different : query≠id) (size : Size) (initial : Row memory query size) :
    Row (source_range_insert_live memory id entry) query size := by
  obtain ⟨old,present,sizeEq⟩:=initial
  exact ⟨old,(GlobalAddressLiveSizeFormation.insert_lookup_other memory id query entry different).trans present,sizeEq⟩

theorem inserted {K} (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) : Row (source_range_insert_live memory id entry) id entry.allocation.byteSize :=
  ⟨entry,MemoryCopyBridge.live_lookup_replaced memory id entry,rfl⟩

theorem remove_other {K} (memory : MemoryState Provenance BorrowTree K) (id query : AllocId)
    (different : query≠id) (size : Size) (initial : Row memory query size) :
    Row (source_memory_remove_live memory id).1 query size := by
  obtain ⟨old,present,sizeEq⟩:=initial
  refine ⟨old,?_,sizeEq⟩
  unfold_internal ".MemoryState.removeLive"
  exact (GlobalAddressLiveSizeFormation.filter_lookup memory id query different).trans present

theorem gc {K} (memory : MemoryState Provenance BorrowTree K) (id : AllocId) (size : Size)
    (initial : Row memory id size) (reachable : Array AllocId) : Row (memory.removeUnreachable reachable) id size := initial

theorem replace_extra {K} (memory : MemoryState Provenance BorrowTree K)
    (id query : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (present : memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (size : Size) (initial : Row memory query size) :
    Row (source_range_insert_live memory id {entry with allocation:=entry.allocation.setExtra tree}) query size := by
  by_cases different : query≠id
  · exact insert_other memory id query _ different size initial
  · have same : query=id := Classical.byContradiction different
    subst query
    obtain ⟨old,found,sizeEq⟩:=initial
    have eq : old=entry:=congrArg Prod.snd (Option.some.inj (found.symm.trans present))
    subst old
    rw [sizeEq]
    exact inserted memory id _
end DuplicatePrefix.GlobalAddressLocalRowFormation
