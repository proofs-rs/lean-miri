import duplicate_prefix.WildcardEmptyHistoryClassification
import duplicate_prefix.WildcardGapResolver

namespace DuplicatePrefix.WildcardEmptyHistoryConsumers
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Exactly the raw address contracts consumed by the existing empty-call
families. The unresolved predecessor and metadata-gap cases share the actual
GapResolver pipeline, including its return-slot metadata transport. -/
def Families {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64) (sizes : AllocId → Size) : Prop :=
  WildcardOrderedMissAddress.Miss addresses address ∨
    (∃ id base,addresses.exposed.contains id=true ∧
      WildcardGeneralHitReborrow.Geometry addresses.intToPtrMap address base id (sizes id)) ∨
    WildcardGapResolver.Miss addresses memory address

/-- No geometric branch or lookup success is selected by the caller. Every
finite managed address history supplies one existing empty-call family. -/
theorem classify {K} [DecidableEq K] (sizes : AllocId → Size)
    {memory : MemoryState Provenance BorrowTree K} {addresses : GlobalAddressState}
    (history : GlobalAddressReuseHistory.History sizes memory addresses) (address : UInt64) :
    Families memory addresses address sizes := by
  rcases WildcardEmptyHistoryClassification.history_classify sizes history address with
    (miss | predecessor) | hit | gap
  · exact Or.inl miss
  · obtain ⟨position,row,size,partition,present,metadata,unexposed⟩ := predecessor
    exact Or.inr (Or.inr (Or.inr ⟨position,row,size,partition,present,
      WildcardMetadataGap.size_of_row memory row.allocId size metadata,unexposed⟩))
  · exact Or.inr (Or.inl hit)
  · exact Or.inr (Or.inr (Or.inl (Or.inl (WildcardMetadataGap.geometry _ address memory gap))))

/-- A family-independent endpoint allows existing physical empty-call proofs
of each raw family to be joined without adding their geometry to Initial.
The continuation conclusion is intentionally arbitrary: this lemma does not
claim physical contracts, global materialization, or MIR traces on its own. -/
theorem dispatch {K} [DecidableEq K] (sizes : AllocId → Size)
    {memory : MemoryState Provenance BorrowTree K} {addresses : GlobalAddressState}
    (history : GlobalAddressReuseHistory.History sizes memory addresses) (address : UInt64)
    (Result : Prop)
    (miss : WildcardOrderedMissAddress.Miss addresses address → Result)
    (hit : ∀ id base,addresses.exposed.contains id=true →
      WildcardGeneralHitReborrow.Geometry addresses.intToPtrMap address base id (sizes id) → Result)
    (gap : WildcardGapResolver.Miss addresses memory address → Result) : Result := by
  rcases classify sizes history address with legacy | ⟨id,base,exposed,geometry⟩ | unresolved
  · exact miss legacy
  · exact hit id base exposed geometry
  · exact gap unresolved
end DuplicatePrefix.WildcardEmptyHistoryConsumers
