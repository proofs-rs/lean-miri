import duplicate_prefix.WildcardGapAddress
import duplicate_prefix.WildcardHitAddress

namespace DuplicatePrefix.WildcardInteriorHitAddress
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Raw inverse-vector partition around an interior address. This describes
stored address geometry, not a successful source search. -/
def Cut (entries : Array InverseAddressEntry) (address : UInt64) (cut : Nat) : Prop :=
  cut ≤ entries.size ∧
  (∀ index (valid : index < entries.size), index < cut → entries[index].address < address) ∧
  (∀ index (valid : index < entries.size), cut ≤ index → address < entries[index].address)

/-- The unchanged source binary search computes the insertion position from
the initial vector's raw address partition, for arbitrary finite vector length. -/
theorem inverse_cut (entries : Array InverseAddressEntry) (address : UInt64) (cut : Nat)
    (geometry : Cut entries address cut) :
    miss_source_inverse_search entries address = (cut,false) := by
  unfold_global_data ".findInverseIndex"
  simp only [Id.run,bind,pure,Id.instMonad,ForIn.forIn]
  name_range_scan
  let invariant : (Nat × Nat × Option Nat) → Prop := fun state =>
    state.1 ≤ cut ∧ cut ≤ state.2.1 ∧ state.2.1 ≤ entries.size ∧ state.2.2 = none
  let final : (Nat × Nat × Option Nat) → Prop := fun state => state.1 = cut ∧ state.2.2 = none
  have step : ∀ state, invariant state →
      (∃ done, scan () state = .done done ∧ final done) ∨
      ∃ next, scan () state = .yield next ∧ invariant next ∧ state.2.1-state.1 > next.2.1-next.1 := by
    intro state good
    rcases state with ⟨low,high,found⟩
    rcases good with ⟨lowCut,cutHigh,bounded,missing⟩
    dsimp only at lowCut cutHigh bounded missing
    subst found
    by_cases nonempty : low < high
    · let middle := low+(high-low)/2
      have lower : low ≤ middle := by omega
      have upper : middle < high := by omega
      have valid : middle < entries.size := by omega
      have lookup : entries[middle]? = some entries[middle] := Array.getElem?_eq_getElem valid
      by_cases before : middle < cut
      · have earlier := geometry.2.1 middle valid before
        refine Or.inr ⟨(middle+1,high,none),?_,⟨by change middle+1 ≤ cut;omega,cutHigh,bounded,rfl⟩,?_⟩
        · simp [scan,nonempty,middle,lookup,earlier]
        · change high-low > high-(middle+1);omega
      · have later := geometry.2.2 middle valid (by omega)
        have notEarlier : ¬ entries[middle].address < address := by
          have greater := UInt64.lt_iff_toNat_lt.mp later
          intro earlier
          have less := UInt64.lt_iff_toNat_lt.mp earlier
          omega
        refine Or.inr ⟨(low,middle,none),?_,⟨lowCut,by change cut ≤ middle;omega,by change middle ≤ entries.size;omega,rfl⟩,?_⟩
        · simp [scan,nonempty,middle,lookup,notEarlier,later]
        · change high-low > middle-low;omega
    · refine Or.inl ⟨(low,high,none),by simp [scan,nonempty],by change low = cut;omega,rfl⟩
  have finished := GeneralRangeMapFind.loop_finished scan (fun state => state.2.1-state.1) invariant final step
    (0,entries.size,none) ⟨Nat.zero_le _,geometry.1,Nat.le_refl _,rfl⟩
  simp only [final] at finished
  simp [finished.1,finished.2]

/-- Ordinary strict ordering of the stored inverse-address vector. -/
def Ordered (entries : Array InverseAddressEntry) : Prop :=
  ∀ left right (lt : left < right) (valid : right < entries.size), entries[left].address < entries[right].address

/-- A sorted inverse map's selected base and next-base bound form the exact
insertion partition. The last allocation has no next-base obligation. -/
theorem cut_of_ordered (entries : Array InverseAddressEntry) (address base : UInt64) (id : AllocId)
    (position : Nat) (valid : position < entries.size) (ordered : Ordered entries)
    (row : entries[position]? = some ⟨base,id⟩) (afterBase : base < address)
    (beforeNext : ∀ nextValid : position+1 < entries.size, address < entries[position+1].address) :
    Cut entries address (position+1) := by
  have actual : entries[position] = ⟨base,id⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans row)
  refine ⟨by omega,?_,?_⟩
  · intro index bounded beforeCut
    by_cases same : index = position
    · subst index
      rw [actual]
      exact afterBase
    · have earlier := ordered index position (by omega) valid
      rw [actual] at earlier
      change entries[index].address < base at earlier
      exact UInt64.lt_iff_toNat_lt.mpr (by
        have first := UInt64.lt_iff_toNat_lt.mp earlier
        have second := UInt64.lt_iff_toNat_lt.mp afterBase
        omega)
  · intro index bounded afterCut
    have nextValid : position+1 < entries.size := by omega
    have next := beforeNext nextValid
    by_cases same : index = position+1
    · subst index
      exact next
    · have later := ordered (position+1) index (by omega) bounded
      exact UInt64.lt_iff_toNat_lt.mpr (by
        have first := UInt64.lt_iff_toNat_lt.mp next
        have second := UInt64.lt_iff_toNat_lt.mp later
        omega)

/-- Any finite inverse vector may have an interior live exposed hit. Only
the chosen predecessor's size/liveness is queried; unrelated rows are arbitrary
subject to the initial address partition. -/
theorem allocation (state : GlobalAddressState) (address base : UInt64) (id : AllocId)
    (hooks : AddressLookupHooks) (size : Size) (position : Nat)
    (mode : state.provenanceMode ≠ .strict)
    (geometry : Cut state.intToPtrMap address (position+1))
    (row : state.intToPtrMap[position]? = some ⟨base,id⟩)
    (known : hooks.sizeOf id = some size) (inside : address-base < size.bytes)
    (exposed : state.exposed.contains id = true) (live : hooks.isLive id = some true) :
    state.allocIdFromAddr address 0 hooks = .ok (some id) := by
  have search := inverse_cut state.intToPtrMap address (position+1) geometry
  have member : id ∈ state.exposed := by simpa using exposed
  unfold GlobalAddressState.allocIdFromAddr
  unfold_global_data ".GlobalAddressState.inverseSearch"
  simp [mode,search,row,known,inside,member,live,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

theorem pointer (state : GlobalAddressState) (address base : UInt64) (id : AllocId)
    (hooks : AddressLookupHooks) (size : Size) (position : Nat)
    (arithmetic : PointerArithmetic) (width : arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : state.provenanceMode ≠ .strict)
    (geometry : Cut state.intToPtrMap address (position+1))
    (row : state.intToPtrMap[position]? = some ⟨base,id⟩)
    (known : hooks.sizeOf id = some size) (inside : address-base < size.bytes)
    (exposed : state.exposed.contains id = true) (live : hooks.isLive id = some true)
    (cached : state.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩) :
    state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0 hooks arithmetic =
      .ok (some (id,Size.ofBytes (address-base))) := by
  subst arithmetic
  unfold GlobalAddressState.ptrGetAlloc
  unfold_internal ".GlobalAddressState.findBase"
  simp only [Pointer.new,Size.ofBytes,allocation state address base id hooks size position mode geometry row known inside exposed live,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,cached,Option.map_some]
  erw [DuplicatePrefix.PointerArithmetic.truncate_u64_identity]
  rfl

/-- Actual typed zero-sized wildcard resolution at a non-base address, from
the inverse-vector geometry and a real live allocation row. No successful
resolution or callback equation is assumed. -/
theorem resolve {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (address base : UInt64) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (position : Nat)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : before.machine.user.addresses.provenanceMode ≠ .strict)
    (geometry : Cut before.machine.user.addresses.intToPtrMap address (position+1))
    (row : before.machine.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (inside : address-base < entry.allocation.byteSize.bytes)
    (exposed : before.machine.user.addresses.exposed.contains id = true)
    (cached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before =
      .ok (some ⟨id,Size.ofBytes (address-base),.wildcard⟩) before := by
  have member := Array.mem_of_find?_eq_some present
  have any : before.machine.memory.live.any (fun row => row.1 == id) = true :=
    Array.any_eq_true'.mpr ⟨(id,entry),member,by simp⟩
  have live : before.machine.memory.isAllocLive id = true := by simp [MemoryState.isAllocLive,any]
  have resolution := pointer before.machine.user.addresses address base id
    (⟨fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size),
      fun id => some (before.machine.memory.isAllocLive id)⟩ : AddressLookupHooks)
    entry.allocation.byteSize position pointers.arithmetic width mode geometry row
    (WildcardGapAddress.size_of_live before.machine.memory id entry present) inside exposed (by simp [live]) cached
  simp only [Pointer.new] at resolution
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,Pointer.new,resolution,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Id.run]

end DuplicatePrefix.WildcardInteriorHitAddress
