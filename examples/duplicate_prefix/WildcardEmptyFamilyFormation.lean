import duplicate_prefix.WildcardEmptyCoherentResolution
import duplicate_prefix.WildcardOrderedMissAddress
import duplicate_prefix.WildcardGeneralHitReborrow
namespace DuplicatePrefix.WildcardEmptyFamilyFormation
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open WildcardInteriorHitAddress (Ordered Cut)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def Apart (entries : Array InverseAddressEntry) (sizes : AllocId → Size) : Prop :=
  ∀ left right (valid : right < entries.size) (less : left < right),
    entries[left].address.toNat + (sizes entries[left].allocId).bytes.toNat ≤ entries[right].address.toNat

theorem below (entries : Array InverseAddressEntry) (address : UInt64) (partition : Cut entries address 0) :
    ∀ row ∈ entries, address < row.address := by
  intro row member
  obtain ⟨index,valid,equal⟩ := Array.mem_iff_getElem.mp member
  simpa only [equal] using partition.2.2 index valid (Nat.zero_le _)

/-- Ordered, physically disjoint allocation ranges turn the selected raw
predecessor's outside bound into the existing all-row metadata-gap contract. -/
theorem gap {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (entries : Array InverseAddressEntry) (address : UInt64) (sizes : AllocId → Size)
    (apart : Apart entries sizes)
    (metadata : ∀ row ∈ entries, WildcardMetadataGap.SizeRow memory row.allocId (sizes row.allocId))
    (cut : Nat) (positive : cut ≠ 0) (partition : Cut entries address cut)
    (last : InverseAddressEntry) (lastPresent : entries[cut-1]? = some last)
    (outside : (sizes last.allocId).bytes ≤ address-last.address) :
    WildcardMetadataGap.Geometry entries address memory := by
  intro row member
  obtain ⟨index,valid,equal⟩ := Array.mem_iff_getElem.mp member
  have lastValid : cut-1 < entries.size := by have bounded:=partition.1;omega
  have lastEq : entries[cut-1] = last := Option.some.inj ((Array.getElem?_eq_getElem lastValid).symm.trans lastPresent)
  have raw := metadata row member
  have lessOrMore := Nat.lt_or_ge index cut
  constructor
  · intro same
    rcases lessOrMore with earlier | later
    · have lt := partition.2.1 index valid earlier
      rw [equal,same] at lt
      exact UInt64.lt_irrefl _ lt
    · have lt := partition.2.2 index valid later
      rw [equal,same] at lt
      exact UInt64.lt_irrefl _ lt
  · intro earlier
    refine ⟨sizes row.allocId,raw,?_⟩
    have before : index < cut := by
      by_cases yes : index < cut
      · exact yes
      · have later := partition.2.2 index valid (by omega)
        rw [equal] at later
        have one:=UInt64.lt_iff_toNat_lt.mp earlier
        have two:=UInt64.lt_iff_toNat_lt.mp later
        omega
    by_cases same : index = cut-1
    · subst index
      have rowEq : row = last := equal.symm.trans lastEq
      subst row
      simpa only [lastEq] using outside
    · have earlierIndex : index < cut-1 := by omega
      have separated := apart index (cut-1) lastValid earlierIndex
      have lastBefore := partition.2.1 (cut-1) lastValid (by omega)
      apply UInt64.le_iff_toNat_le.mpr
      rw [UInt64.toNat_sub_of_le address row.address (UInt64.le_iff_toNat_le.mpr (by
        have lt:=UInt64.lt_iff_toNat_lt.mp earlier;omega))]
      rw [equal] at separated
      have lt := UInt64.lt_iff_toNat_lt.mp lastBefore
      omega

/-- Address geometry from raw ordered, disjoint, metadata-backed state forms
existing miss/hit/gap inputs, or identifies the still-separate unexposed
interior branch. This concerns address geometry only; physical call and TB
history resources are not inferred from shallow typed validity. -/
theorem classify {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64) (sizes : AllocId → Size)
    (ordered : Ordered addresses.intToPtrMap) (apart : Apart addresses.intToPtrMap sizes)
    (metadata : ∀ row ∈ addresses.intToPtrMap, WildcardMetadataGap.SizeRow memory row.allocId (sizes row.allocId)) :
    WildcardOrderedMissAddress.Miss addresses address ∨
    (∃ id base, addresses.exposed.contains id = true ∧
      WildcardGeneralHitReborrow.Geometry addresses.intToPtrMap address base id (sizes id)) ∨
    WildcardMetadataGap.Geometry addresses.intToPtrMap address memory ∨
    ∃ position row, addresses.exposed.contains row.allocId = false ∧
      Cut addresses.intToPtrMap address (position+1) ∧ addresses.intToPtrMap[position]? = some row ∧
      address-row.address < (sizes row.allocId).bytes := by
  rcases WildcardEmptyAddressClassification.inverse_partition addresses.intToPtrMap address ordered with
    ⟨position,row,valid,present,equal,search⟩ | ⟨cut,search,partition⟩
  · have shape : row = ⟨address,row.allocId⟩ := by cases row with | mk a id => cases equal; rfl
    have raw : addresses.intToPtrMap[position]? = some ⟨address,row.allocId⟩ := present.trans (congrArg some shape)
    cases exposed : addresses.exposed.contains row.allocId with
    | false => exact Or.inl (Or.inr ⟨row.allocId,position,valid,ordered,raw,exposed⟩)
    | true => exact Or.inr (Or.inl ⟨row.allocId,address,exposed,Or.inl ⟨rfl,position,valid,ordered,raw⟩⟩)
  · by_cases zero : cut = 0
    · subst cut
      exact Or.inl (Or.inl (below addresses.intToPtrMap address partition))
    · have valid : cut-1 < addresses.intToPtrMap.size := by have bounded:=partition.1;omega
      let row := addresses.intToPtrMap[cut-1]
      have present : addresses.intToPtrMap[cut-1]? = some row := Array.getElem?_eq_getElem valid
      have cutEq : cut-1+1 = cut := by omega
      by_cases inside : address-row.address < (sizes row.allocId).bytes
      · cases exposed : addresses.exposed.contains row.allocId with
        | false => exact Or.inr (Or.inr (Or.inr ⟨cut-1,row,exposed,cutEq ▸ partition,present,inside⟩))
        | true =>
          have shape : row = ⟨row.address,row.allocId⟩ := by cases row;rfl
          have raw : addresses.intToPtrMap[cut-1]? = some ⟨row.address,row.allocId⟩ := present.trans (congrArg some shape)
          exact Or.inr (Or.inl ⟨row.allocId,row.address,exposed,Or.inr ⟨cut-1,cutEq ▸ partition,raw,inside⟩⟩)
      · apply Or.inr;apply Or.inr;apply Or.inl
        apply gap memory addresses.intToPtrMap address sizes apart metadata cut zero partition row present
        exact UInt64.le_iff_toNat_le.mpr (by
          have noLt : ¬(address-row.address).toNat < (sizes row.allocId).bytes.toNat := by
            simpa only [UInt64.lt_iff_toNat_lt] using inside
          omega)

end DuplicatePrefix.WildcardEmptyFamilyFormation
