import duplicate_prefix.GlobalAddressRangeFormation
import duplicate_prefix.MemoryCopyBridge
namespace DuplicatePrefix.GlobalAddressLiveSizeFormation
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Raw live data/global size suppliers. Dead rows are deliberately absent:
address histories free their inverse rows before adding dead metadata. -/
inductive Row {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId) : Size → Prop where
  | localRow (entry : LocalAllocation Provenance BorrowTree K)
      (present : memory.live.find? (fun row => row.1 == id) = some (id,entry)) : Row memory id entry.allocation.byteSize
  | globalRow (descriptor : GlobalAllocation)
      (absent : memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : memory.hasFunctionPointer id = false) (noVaList : memory.hasVaListId id = false)
      (present : memory.findGlobal? id = some descriptor)
      (kind : descriptor.kind = .memory ∨ descriptor.kind = .static) : Row memory id descriptor.size

theorem sizeRow {K} (memory : MemoryState Provenance BorrowTree K) (id : AllocId) (size : Size)
    (row : Row memory id size) : WildcardMetadataGap.SizeRow memory id size := by
  cases row with
  | localRow entry present => exact .live entry present
  | globalRow descriptor absent noFunction noVaList present kind => exact .global descriptor absent noFunction noVaList present kind

open Lean Elab in
elab "source_range_insert_live" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".MemoryState.insertLive" then some name else none
  let [name] := names | throwError "expected source memory insertLive"
  Lean.Meta.mkConstWithFreshMVarLevels name

theorem filter_lookup {K} (memory : MemoryState Provenance BorrowTree K) (id query : AllocId) (different : query ≠ id) :
    (memory.live.filter (fun row => row.1 != id)).find? (fun row => row.1 == query) = memory.live.find? (fun row => row.1 == query) := by
  rw [Array.find?_filter]
  congr 1
  funext row
  by_cases same : row.1 = query
  · simp [same,different]
  · simp [same]

theorem insert_lookup_other {K} (memory : MemoryState Provenance BorrowTree K)
    (id query : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (different : query ≠ id) :
    (source_range_insert_live memory id entry).live.find? (fun row => row.1 == query) = memory.live.find? (fun row => row.1 == query) := by
  unfold_internal ".MemoryState.insertLive"
  simp only [Array.find?_push,show (id == query) = false from by simpa using Ne.symm different,Bool.false_eq_true,↓reduceIte,Option.or_none]
  exact filter_lookup memory id query different

theorem insert_other {K} (memory : MemoryState Provenance BorrowTree K)
    (id query : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (different : query ≠ id)
    (size : Size) (initial : Row memory query size) : Row (source_range_insert_live memory id entry) query size := by
  have frame := insert_lookup_other memory id query entry different
  cases initial with
  | localRow old present => exact .localRow old (frame.trans present)
  | globalRow descriptor absent noFunction noVaList present kind =>
    exact .globalRow descriptor (frame.trans absent) noFunction noVaList present kind

theorem remove_other {K} (memory : MemoryState Provenance BorrowTree K)
    (id query : AllocId) (different : query ≠ id) (size : Size) (initial : Row memory query size) :
    Row (source_memory_remove_live memory id).1 query size := by
  have frame : (source_memory_remove_live memory id).1.live.find? (fun row => row.1 == query) = memory.live.find? (fun row => row.1 == query) := by
    unfold_internal ".MemoryState.removeLive"
    exact filter_lookup memory id query different
  cases initial with
  | localRow old present => exact .localRow old (frame.trans present)
  | globalRow descriptor absent noFunction noVaList present kind =>
    exact .globalRow descriptor (frame.trans absent) noFunction noVaList present kind

theorem inserted {K} (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) :
    Row (source_range_insert_live memory id entry) id entry.allocation.byteSize :=
  .localRow entry (MemoryCopyBridge.live_lookup_replaced memory id entry)

theorem gc {K} (memory : MemoryState Provenance BorrowTree K) (id : AllocId) (size : Size)
    (initial : Row memory id size) (reachable : Array AllocId) : Row (memory.removeUnreachable reachable) id size := by
  cases initial with
  | localRow entry present => exact .localRow entry present
  | globalRow descriptor absent noFunction noVaList present kind => exact .globalRow descriptor absent noFunction noVaList present kind

/-- The source tree-extra replacement used by retagging and every GC row keeps
physical byte sizes. It may change the complete borrow tree. -/
theorem replace_extra {K} (memory : MemoryState Provenance BorrowTree K)
    (id query : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : Size) (initial : Row memory query size) :
    Row (source_range_insert_live memory id {entry with allocation:=entry.allocation.setExtra tree}) query size := by
  by_cases different : query ≠ id
  · exact insert_other memory id query _ different size initial
  · have same : query = id := by
      by_cases equal : query = id
      · exact equal
      · exact False.elim (different equal)
    subst query
    cases initial with
    | localRow old found =>
      have same : old=entry := congrArg Prod.snd (Option.some.inj (found.symm.trans present))
      subst old
      exact inserted memory id _
    | globalRow descriptor absent noFunction noVaList found kind => rw [present] at absent;cases absent

end DuplicatePrefix.GlobalAddressLiveSizeFormation
