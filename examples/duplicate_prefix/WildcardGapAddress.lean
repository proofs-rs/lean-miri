import duplicate_prefix.WildcardMissAddress

namespace DuplicatePrefix.WildcardGapAddress
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Explicit inverse-map geometry and predecessor size metadata. An address
may lie in any gap or after the final allocation. This is not a successful
pointer-lookup premise; exact base hits are excluded by data. -/
def Geometry (entries : Array InverseAddressEntry) (address : UInt64)
    (sizeOf : AllocId → Option Size) : Prop :=
  ∀ row ∈ entries, row.address ≠ address ∧
    (row.address < address → ∃ size, sizeOf row.allocId = some size ∧ ¬ address-row.address < size.bytes)

/-- Even without assuming sortedness, a missing exact address makes the actual
binary search return a bounded insertion index. Any predecessor it selects was
actually tested below the target, so the metadata condition applies to it. -/
theorem inverse_missing (entries : Array InverseAddressEntry) (address : UInt64)
    (different : ∀ row ∈ entries, row.address ≠ address) :
    ∃ position, miss_source_inverse_search entries address = (position,false) ∧ position ≤ entries.size ∧
      (position ≠ 0 → ∃ row, entries[position-1]? = some row ∧ row.address < address) := by
  unfold_global_data ".findInverseIndex"
  simp only [Id.run,bind,pure,Id.instMonad,ForIn.forIn]
  name_range_scan
  let invariant : (Nat × Nat × Option Nat) → Prop := fun state =>
    state.1 ≤ state.2.1 ∧ state.2.1 ≤ entries.size ∧ state.2.2 = none ∧
      (state.1 ≠ 0 → ∃ row, entries[state.1-1]? = some row ∧ row.address < address)
  let final := fun state : Nat × Nat × Option Nat =>
    state.1 ≤ entries.size ∧ state.2.2 = none ∧
      (state.1 ≠ 0 → ∃ row, entries[state.1-1]? = some row ∧ row.address < address)
  have step : ∀ state, invariant state →
      (∃ done, scan () state = .done done ∧ final done) ∨
      ∃ next, scan () state = .yield next ∧ invariant next ∧ next.2.1-next.1 < state.2.1-state.1 := by
    intro state good
    rcases state with ⟨low,high,found⟩
    obtain ⟨ordered,bounded,missing,predecessor⟩ := good
    dsimp only at ordered bounded missing predecessor
    subst found
    by_cases nonempty : low < high
    · let middle := low+(high-low)/2
      have atLeast : low ≤ middle := by omega
      have before : middle < high := by omega
      have valid : middle < entries.size := by omega
      have lookup : entries[middle]? = some entries[middle] := Array.getElem?_eq_getElem valid
      have distinct := different entries[middle] (Array.getElem_mem valid)
      by_cases earlier : entries[middle].address < address
      · refine Or.inr ⟨(middle+1,high,none),?_,?_,by change high-(middle+1) < high-low;omega⟩
        · simp [scan,nonempty,middle,lookup,earlier]
        · refine ⟨?_,bounded,rfl,?_⟩
          · change middle+1 ≤ high;omega
          · intro positive
            exact ⟨entries[middle],by simpa only [Nat.add_sub_cancel] using lookup,earlier⟩
      · have later : address < entries[middle].address := by
          apply UInt64.lt_iff_toNat_lt.mpr
          have ne : entries[middle].address.toNat ≠ address.toNat := fun equal => distinct (UInt64.toNat_inj.mp equal)
          have notEarlier : ¬entries[middle].address.toNat < address.toNat := by simpa only [UInt64.lt_iff_toNat_lt] using earlier
          omega
        refine Or.inr ⟨(low,middle,none),?_,⟨atLeast,by change middle ≤ entries.size;omega,rfl,predecessor⟩,by change middle-low < high-low;omega⟩
        simp [scan,nonempty,middle,lookup,earlier,later]
    · refine Or.inl ⟨(low,high,none),by simp [scan,nonempty],?_,rfl,predecessor⟩
      change low ≤ entries.size
      omega
  have result := GeneralRangeMapFind.loop_finished scan (fun state => state.2.1-state.1) invariant final step
    (0,entries.size,none) ⟨Nat.zero_le _,Nat.le_refl _,rfl,by intro impossible;exact False.elim (impossible rfl)⟩
  exact ⟨_,by simp [result.2.1],result.1,result.2.2⟩

/-- Actual default/permissive zero-byte lookup returns unresolved in every
geometry-certified gap/after-last case. Size metadata is consulted when the
source algorithm selects a predecessor, exactly as in the pinned semantics. -/
theorem allocation (state : GlobalAddressState) (address : UInt64) (hooks : AddressLookupHooks)
    (mode : state.provenanceMode ≠ .strict) (geometry : Geometry state.intToPtrMap address hooks.sizeOf) :
    state.allocIdFromAddr address 0 hooks = .ok none := by
  obtain ⟨position,search,bound,predecessor⟩ := inverse_missing state.intToPtrMap address (fun row member => (geometry row member).1)
  unfold GlobalAddressState.allocIdFromAddr
  unfold_global_data ".GlobalAddressState.inverseSearch"
  by_cases zero : position = 0
  · simp [mode,search,zero,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  · obtain ⟨row,lookup,earlier⟩ := predecessor zero
    have member : row ∈ state.intToPtrMap := Array.mem_of_getElem? lookup
    obtain ⟨size,known,outside⟩ := (geometry row member).2 earlier
    simp [mode,search,zero,lookup,known,outside,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

/-- The one-row after-last case has a direct size/range data contract. -/
theorem singleton_after (state : GlobalAddressState) (address base : UInt64) (id : AllocId)
    (hooks : AddressLookupHooks) (size : Size) (mode : state.provenanceMode ≠ .strict)
    (mapping : state.intToPtrMap = #[⟨base,id⟩]) (known : hooks.sizeOf id = some size)
    (before : base < address) (outside : size.bytes ≤ address-base) :
    state.allocIdFromAddr address 0 hooks = .ok none := by
  apply allocation state address hooks mode
  intro row member
  rw [mapping] at member
  have same := Array.mem_singleton.mp member
  subst row
  change base ≠ address ∧ (base < address → ∃ size, hooks.sizeOf id = some size ∧ ¬ address-base < size.bytes)
  exact ⟨(fun same => by simp only [same,UInt64.lt_iff_toNat_lt,Nat.lt_irrefl] at before),
    fun _ => ⟨size,known,by intro inside;have a := UInt64.le_iff_toNat_le.mp outside;have b := UInt64.lt_iff_toNat_lt.mp inside;omega⟩⟩

/-- A gap between two inverse bases needs size metadata only for the left
candidate; the right row is strictly above the address and is never sized. -/
theorem two_row_middle (state : GlobalAddressState) (address left right : UInt64) (leftId rightId : AllocId)
    (hooks : AddressLookupHooks) (size : Size) (mode : state.provenanceMode ≠ .strict)
    (mapping : state.intToPtrMap = #[⟨left,leftId⟩,⟨right,rightId⟩]) (known : hooks.sizeOf leftId = some size)
    (before : left < address) (after : address < right) (outside : size.bytes ≤ address-left) :
    state.allocIdFromAddr address 0 hooks = .ok none := by
  apply allocation state address hooks mode
  intro row member
  rw [mapping] at member
  have cases : row = ⟨left,leftId⟩ ∨ row = ⟨right,rightId⟩ := by
    simpa [Array.mem_def] using member
  rcases cases with rfl | rfl
  · change left ≠ address ∧ (left < address → ∃ size, hooks.sizeOf leftId = some size ∧ ¬ address-left < size.bytes)
    exact ⟨(fun same => by simp only [same,UInt64.lt_iff_toNat_lt,Nat.lt_irrefl] at before),
      fun _ => ⟨size,known,by intro inside;have a := UInt64.le_iff_toNat_le.mp outside;have b := UInt64.lt_iff_toNat_lt.mp inside;omega⟩⟩
  · change right ≠ address ∧ (right < address → ∃ size, hooks.sizeOf rightId = some size ∧ ¬ address-right < size.bytes)
    refine ⟨(fun same => by simp only [same,UInt64.lt_iff_toNat_lt,Nat.lt_irrefl] at after),?_⟩
    intro earlier
    have a := UInt64.lt_iff_toNat_lt.mp earlier
    have b := UInt64.lt_iff_toNat_lt.mp after
    omega

theorem pointer (state : GlobalAddressState) (address : UInt64) (hooks : AddressLookupHooks)
    (arithmetic : PointerArithmetic) (mode : state.provenanceMode ≠ .strict)
    (geometry : Geometry state.intToPtrMap address hooks.sizeOf) :
    state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0 hooks arithmetic = .ok none := by
  simp only [GlobalAddressState.ptrGetAlloc,Pointer.new,Size.ofBytes,allocation state address hooks mode geometry,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

/-- Geometry plus actual allocation-size metadata suffices for the typed
zero-sized resolver too. No successful resolver callback is an input. -/
theorem resolve {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (address : UInt64)
    (mode : before.machine.user.addresses.provenanceMode ≠ .strict)
    (geometry : Geometry before.machine.user.addresses.intToPtrMap address
      (fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size))) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before =
      .ok none before := by
  have resolution := pointer before.machine.user.addresses address
    (⟨fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size),
      fun id => some (before.machine.memory.isAllocLive id)⟩ : AddressLookupHooks)
    pointers.arithmetic mode geometry
  simp only [Pointer.new] at resolution
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,Pointer.new,resolution,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Id.run]

/-- Canonical memory's live allocation row determines size metadata directly.
This is an equation about stored metadata, not physical memory-operation success. -/
theorem size_of_live {K : Type} (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (id : AllocId) (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    (memory.getAllocInfo id).toOption.map (·.size) = some entry.allocation.byteSize := by
  unfold MemoryState.getAllocInfo
  rw [present]
  rfl

/-- Gap geometry expressed entirely in canonical initial-state data: inverse
rows, live allocation rows, byte sizes and address inequalities. -/
def LiveGeometry {K : Type} (entries : Array InverseAddressEntry) (address : UInt64)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K) : Prop :=
  ∀ row ∈ entries, row.address ≠ address ∧ (row.address < address →
    ∃ entry, memory.live.find? (fun cell => cell.1 == row.allocId) = some (row.allocId,entry) ∧
      entry.allocation.byteSize.bytes ≤ address-row.address)

theorem geometry_of_live {K : Type} (entries : Array InverseAddressEntry) (address : UInt64)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (initial : LiveGeometry entries address memory) :
    Geometry entries address (fun id => (memory.getAllocInfo id).toOption.map (·.size)) := by
  intro row member
  have data := initial row member
  refine ⟨data.1,?_⟩
  intro earlier
  obtain ⟨entry,present,outside⟩ := data.2 earlier
  refine ⟨entry.allocation.byteSize,size_of_live memory row.allocId entry present,?_⟩
  intro inside
  have lower := UInt64.le_iff_toNat_le.mp outside
  have upper := UInt64.lt_iff_toNat_lt.mp inside
  omega

/-- Actual typed zero-byte resolution in any canonical live-data-certified gap
or after-last position; no successful metadata/resolver operation is supplied. -/
theorem resolve_live {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (address : UInt64)
    (mode : before.machine.user.addresses.provenanceMode ≠ .strict)
    (initial : LiveGeometry before.machine.user.addresses.intToPtrMap address before.machine.memory) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before =
      .ok none before :=
  resolve pointers before address mode (geometry_of_live before.machine.user.addresses.intToPtrMap address before.machine.memory initial)

end DuplicatePrefix.WildcardGapAddress
