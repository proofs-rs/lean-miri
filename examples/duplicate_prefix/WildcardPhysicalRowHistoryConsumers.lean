import duplicate_prefix.GlobalAddressPhysicalRowHistory
import duplicate_prefix.WildcardEmptyHistoryConsumers
namespace DuplicatePrefix.WildcardPhysicalRowHistoryConsumers
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Actual fresh physical insertion may interleave arbitrary managed
allocation/free/exposure/GC steps. Every resulting address still belongs to
an existing empty-call consumer family, without a supplied geometric case. -/
theorem classify {K} [DecidableEq K] (sizes : AllocId → Size)
    {memory : MemoryState Provenance BorrowTree K} {addresses : GlobalAddressState}
    (history : GlobalAddressPhysicalRowHistory.History sizes memory addresses) (address : UInt64) :
    WildcardEmptyHistoryConsumers.Families memory addresses address sizes := by
  obtain ⟨generation,initial⟩:=GlobalAddressPhysicalRowHistory.invariant sizes history
  rcases WildcardEmptyHistoryClassification.state_classify memory addresses generation sizes initial address with
    (miss | predecessor) | hit | gap
  · exact Or.inl miss
  · obtain ⟨position,row,size,partition,present,metadata,unexposed⟩:=predecessor
    exact Or.inr (Or.inr (Or.inr ⟨position,row,size,partition,present,
      WildcardMetadataGap.size_of_row memory row.allocId size metadata,unexposed⟩))
  · exact Or.inr (Or.inl hit)
  · exact Or.inr (Or.inr (Or.inl (Or.inl (WildcardMetadataGap.geometry _ address memory gap))))

/-- The actual zero-byte allocation lookup completes under nonstrict
provenance after every physical-row history prefix. This is lookup totality,
not a claim that all physical whole-call contracts have been formed. -/
theorem total {K} [DecidableEq K] (sizes : AllocId → Size)
    {memory : MemoryState Provenance BorrowTree K} {addresses : GlobalAddressState}
    (history : GlobalAddressPhysicalRowHistory.History sizes memory addresses) (address : UInt64)
    (mode : addresses.provenanceMode≠.strict) :
    ∃ result,addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup memory)=.ok result := by
  obtain ⟨generation,initial⟩:=GlobalAddressPhysicalRowHistory.invariant sizes history
  apply WildcardEmptyCoherentResolution.total memory addresses address initial.resources.recurring mode
  intro row member
  exact WildcardEmptyHistoryClassification.row_supplier memory row.allocId (sizes row.allocId)
    (initial.resources.rows row member)
end DuplicatePrefix.WildcardPhysicalRowHistoryConsumers
