import duplicate_prefix.WildcardEmptyFamilyFormation
import duplicate_prefix.GlobalAddressRecurringFormation
namespace DuplicatePrefix.GlobalAddressRangeFormation
open Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open WildcardEmptyFamilyFormation (Apart)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Numeric physical placement, before any source cache insertion. It permits
fresh allocation or reuse of a freed hole, and does not assume cache success. -/
def Placement (entries : Array InverseAddressEntry) (sizes : AllocId → Size)
    (id : AllocId) (address : UInt64) (cut : Nat) : Prop :=
  (∀ index (valid : index < entries.size), index < cut →
    entries[index].address.toNat + (sizes entries[index].allocId).bytes.toNat ≤ address.toNat) ∧
  (∀ index (valid : index < entries.size), cut ≤ index →
    address.toNat + (sizes id).bytes.toNat ≤ entries[index].address.toNat)

theorem insert (entries : Array InverseAddressEntry) (sizes : AllocId → Size)
    (initial : Apart entries sizes) (id : AllocId) (address : UInt64) (cut : Nat)
    (bounded : cut ≤ entries.size) (placement : Placement entries sizes id address cut) :
    Apart (entries.insertIdx cut ⟨address,id⟩ bounded) sizes := by
  intro left right valid less
  have rightBound : right < entries.size+1 := by simpa only [Array.size_insertIdx] using valid
  have leftBound : left < entries.size+1 := by omega
  rw [Array.getElem_insertIdx bounded (by simpa only [Array.size_insertIdx] using leftBound),
    Array.getElem_insertIdx bounded valid]
  by_cases beforeLeft : left < cut
  · simp only [beforeLeft,↓reduceDIte]
    by_cases beforeRight : right < cut
    · simp only [beforeRight,↓reduceDIte]
      exact initial left right (by omega) less
    · simp only [beforeRight,↓reduceDIte]
      by_cases equalRight : right = cut
      · simp only [equalRight,↓reduceDIte]
        exact placement.1 left (by omega) beforeLeft
      · simp only [equalRight,↓reduceDIte]
        have one := placement.1 left (by omega) beforeLeft
        have two := placement.2 (right-1) (by omega) (by omega)
        omega
  · simp only [beforeLeft,↓reduceDIte]
    have notRight : ¬right < cut := by omega
    have differentRight : right ≠ cut := by omega
    simp only [notRight,differentRight,↓reduceDIte]
    by_cases equalLeft : left = cut
    · simp only [equalLeft,↓reduceDIte]
      exact placement.2 (right-1) (by omega) (by omega)
    · simp only [equalLeft,↓reduceDIte]
      exact initial (left-1) (right-1) (by omega) (by omega)

/-- Source cache insertion computes its position itself and completes from
raw address geometry; both new-allocation and released-hole choices obey the
same numeric placement contract. -/
theorem cache (addresses : GlobalAddressState) (sizes : AllocId → Size)
    (initial : Apart addresses.intToPtrMap sizes) (id : AllocId) (address : UInt64)
    (uncached : addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (nonzero : address ≠ 0) (cut : Nat)
    (partition : WildcardInteriorHitAddress.Cut addresses.intToPtrMap address cut)
    (placement : Placement addresses.intToPtrMap sizes id address cut) :
    (addresses.cacheAddress id address).outcome = .ok () ∧
    Apart (addresses.cacheAddress id address).state.intToPtrMap sizes := by
  have search := WildcardInteriorHitAddress.inverse_cut addresses.intToPtrMap address cut partition
  have nonzeroBool : (address == 0) = false := by simpa using nonzero
  unfold GlobalAddressState.cacheAddress
  unfold_internal ".GlobalAddressState.findBase"
  simp only [uncached,Option.map_none,search,nonzeroBool,Bool.false_eq_true,↓reduceIte,partition.1,↓reduceDIte]
  exact ⟨rfl,insert addresses.intToPtrMap sizes initial id address cut partition.1 placement⟩

theorem erase (entries : Array InverseAddressEntry) (sizes : AllocId → Size)
    (initial : Apart entries sizes) (position : Nat) (valid : position < entries.size) :
    Apart (entries.eraseIdx position valid) sizes := by
  intro left right rightValid less
  have size : (entries.eraseIdx position valid).size = entries.size-1 := Array.size_eraseIdx position valid
  have leftValid : left < (entries.eraseIdx position valid).size := by omega
  rw [Array.getElem_eraseIdx valid leftValid,Array.getElem_eraseIdx valid rightValid]
  split <;> split
  all_goals apply initial <;> omega

/-- Real free removes its inverse row before reuse-pool updates, including
pool-error prefixes. No free outcome is assumed or counted as success. -/
theorem free (addresses : GlobalAddressState) (sizes : AllocId → Size)
    (initial : Apart addresses.intToPtrMap sizes) (ordered : WildcardInteriorHitAddress.Ordered addresses.intToPtrMap)
    (id : AllocId) (base : UInt64) (position : Nat) (valid : position < addresses.intToPtrMap.size)
    (row : addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (cached : addresses.baseAddr.find? (fun entry => entry.allocId == id) = some ⟨id,base⟩)
    (size : Size) (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId)
    (reuseChoice : Bool) (clock : Unit → VClock) :
    Apart (addresses.freeAllocId id size align kind thread reuseChoice clock).state.intToPtrMap sizes := by
  rw [(GlobalAddressFreeHistoryFormation.free_erases addresses id base position valid ordered row cached size align kind thread reuseChoice clock).1]
  exact erase addresses.intToPtrMap sizes initial position valid

theorem expose (addresses : GlobalAddressState) (sizes : AllocId → Size)
    (initial : Apart addresses.intToPtrMap sizes) (provenance : Provenance)
    (live : Option Bool) (tracking : Bool) (hook : Option (Except String Unit)) :
    Apart (addresses.exposeProvenance provenance live tracking hook).state.intToPtrMap sizes := by
  rw [GlobalAddressExposureFormation.expose_inverse]
  exact initial

theorem gc (addresses : GlobalAddressState) (sizes : AllocId → Size) (reachable : Array AllocId)
    (initial : Apart addresses.intToPtrMap sizes) :
    Apart (addresses.removeUnreachableAllocs reachable).intToPtrMap sizes := initial

end DuplicatePrefix.GlobalAddressRangeFormation
