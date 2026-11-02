import duplicate_prefix.WildcardGapAddress

/-! Gap lookup uses allocation-size metadata, including dead rows and lazy
compiler STATIC/MEMORY descriptors. It does not materialize a global or access
dead memory. Raw row precedence is explicit; no successful lookup is assumed.
These contracts alone make no claim about reachability from Rust histories. -/
namespace DuplicatePrefix.WildcardMetadataGap
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows

/-- Initial metadata rows sufficient to compute the actual size query. -/
inductive SizeRow {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId) : Size → Prop
  | live (entry : LocalAllocation Provenance BorrowTree K)
      (present : memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
      SizeRow memory id entry.allocation.byteSize
  | global (descriptor : GlobalAllocation)
      (absent : memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : memory.hasFunctionPointer id = false)
      (noVaList : memory.hasVaListId id = false)
      (present : memory.findGlobal? id = some descriptor)
      (kind : descriptor.kind = .memory ∨ descriptor.kind = .static) :
      SizeRow memory id descriptor.size
  | dead (entry : DeadAllocation)
      (absent : memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : memory.hasFunctionPointer id = false)
      (noVaList : memory.hasVaListId id = false)
      (noGlobal : memory.findGlobal? id = none)
      (present : memory.dead.find? (fun row => row.allocId == id) = some entry) :
      SizeRow memory id entry.size

theorem size_of_row {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (size : Size) (row : SizeRow memory id size) :
    (memory.getAllocInfo id).toOption.map (·.size) = some size := by
  cases row with
  | live entry present => exact WildcardGapAddress.size_of_live memory id entry present
  | global descriptor absent noFunction noVaList present kind =>
    unfold MemoryState.hasVaListId at noVaList
    rcases kind with kind | kind <;>
      simp only [MemoryState.getAllocInfo,absent,noFunction,noVaList,present,kind,
        Bool.false_eq_true, ↓reduceIte] <;> rfl
  | dead entry absent noFunction noVaList noGlobal present =>
    unfold MemoryState.hasVaListId at noVaList
    simp only [MemoryState.getAllocInfo,absent,noFunction,noVaList,noGlobal,present,
      Bool.false_eq_true, ↓reduceIte]
    rfl

def Geometry {K : Type} (entries : Array InverseAddressEntry) (address : UInt64)
    (memory : MemoryState Provenance BorrowTree K) : Prop :=
  ∀ row ∈ entries, row.address ≠ address ∧ (row.address < address →
    ∃ size, SizeRow memory row.allocId size ∧ size.bytes ≤ address-row.address)

theorem geometry {K : Type} (entries : Array InverseAddressEntry) (address : UInt64)
    (memory : MemoryState Provenance BorrowTree K) (initial : Geometry entries address memory) :
    WildcardGapAddress.Geometry entries address (fun id => (memory.getAllocInfo id).toOption.map (·.size)) := by
  intro row member
  refine ⟨(initial row member).1,?_⟩
  intro earlier
  obtain ⟨size,metadata,outside⟩ := (initial row member).2 earlier
  refine ⟨size,size_of_row memory row.allocId size metadata,?_⟩
  intro inside
  have lower := UInt64.le_iff_toNat_le.mp outside
  have upper := UInt64.lt_iff_toNat_lt.mp inside
  omega
end DuplicatePrefix.WildcardMetadataGap
