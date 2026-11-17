import duplicate_prefix.WildcardInteriorHitAddress

namespace DuplicatePrefix.WildcardOrderedHitAddress
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefix.WildcardInteriorHitAddress (Ordered)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Every actual row in an arbitrary finite strictly ordered inverse vector is
found by the unchanged binary search. No search-result premise is supplied. -/
theorem inverse_hit (entries : Array InverseAddressEntry) (base : UInt64) (id : AllocId)
    (position : Nat) (valid : position < entries.size) (ordered : Ordered entries)
    (row : entries[position]? = some ⟨base,id⟩) :
    miss_source_inverse_search entries base = (position,true) := by
  have actual : entries[position] = ⟨base,id⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans row)
  unfold_global_data ".findInverseIndex"
  simp only [Id.run,bind,pure,Id.instMonad,ForIn.forIn]
  name_range_scan
  let invariant : (Nat × Nat × Option Nat) → Prop := fun state =>
    state.1 ≤ state.2.1 ∧ state.2.1 ≤ entries.size ∧
    match state.2.2 with
    | none => state.1 ≤ position ∧ position < state.2.1
    | some found => found = position
  let final : (Nat × Nat × Option Nat) → Prop := fun state => state.2.2 = some position
  let measure : (Nat × Nat × Option Nat) → Nat := fun state =>
    if state.2.2.isNone then state.2.1-state.1+1 else 0
  have step : ∀ state, invariant state →
      (∃ done, scan () state = .done done ∧ final done) ∨
      ∃ next, scan () state = .yield next ∧ invariant next ∧ measure next < measure state := by
    intro state good
    rcases state with ⟨low,high,found⟩
    rcases good with ⟨order,bounded,selection⟩
    dsimp only at order bounded selection
    cases found with
    | some found =>
      subst found
      exact Or.inl ⟨(low,high,some position),by simp [scan],rfl⟩
    | none =>
      have nonempty : low < high := by omega
      let middle := low+(high-low)/2
      have lower : low ≤ middle := by omega
      have upper : middle < high := by omega
      have middleValid : middle < entries.size := by omega
      have lookup : entries[middle]? = some entries[middle] := Array.getElem?_eq_getElem middleValid
      rcases Nat.lt_trichotomy middle position with earlier | same | later
      · have before := ordered middle position earlier valid
        rw [actual] at before
        change entries[middle].address < base at before
        refine Or.inr ⟨(middle+1,high,none),?_,?_,?_⟩
        · simp [scan,nonempty,middle,lookup,before]
        · change middle+1 ≤ high ∧ high ≤ entries.size ∧ middle+1 ≤ position ∧ position < high
          omega
        · change high-(middle+1)+1 < high-low+1
          omega
      · have equal : entries[middle].address = base := by
          simpa only [same] using congrArg InverseAddressEntry.address actual
        refine Or.inr ⟨(low,high,some middle),?_,?_,?_⟩
        · simp [scan,nonempty,middle,lookup,equal]
        · exact ⟨order,bounded,same⟩
        · change 0 < high-low+1
          omega
      · have after := ordered position middle later middleValid
        rw [actual] at after
        change base < entries[middle].address at after
        have notBefore : ¬ entries[middle].address < base := by
          have greater := UInt64.lt_iff_toNat_lt.mp after
          intro before
          have less := UInt64.lt_iff_toNat_lt.mp before
          omega
        refine Or.inr ⟨(low,middle,none),?_,?_,?_⟩
        · simp [scan,nonempty,middle,lookup,notBefore,after]
        · change low ≤ middle ∧ middle ≤ entries.size ∧ low ≤ position ∧ position < middle
          omega
        · change middle-low+1 < high-low+1
          omega
  have finished := GeneralRangeMapFind.loop_finished scan measure invariant final step
    (0,entries.size,none) ⟨Nat.zero_le _,Nat.le_refl _,Nat.zero_le _,valid⟩
  simp only [final] at finished
  simp [finished]

/-- General exact-base live exposed resolution; arbitrary unrelated preceding
and following inverse rows are accepted under raw strict ordering. Unlike an
interior hit, an exact hit does not query allocation size. -/
theorem allocation (state : GlobalAddressState) (base : UInt64) (id : AllocId)
    (hooks : AddressLookupHooks) (position : Nat) (valid : position < state.intToPtrMap.size)
    (ordered : Ordered state.intToPtrMap) (row : state.intToPtrMap[position]? = some ⟨base,id⟩)
    (mode : state.provenanceMode ≠ .strict)
    (exposed : state.exposed.contains id = true) (live : hooks.isLive id = some true) :
    state.allocIdFromAddr base 0 hooks = .ok (some id) := by
  have member : id ∈ state.exposed := by simpa using exposed
  have search := inverse_hit state.intToPtrMap base id position valid ordered row
  unfold GlobalAddressState.allocIdFromAddr
  unfold_global_data ".GlobalAddressState.inverseSearch"
  simp [mode,search,row,member,live,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

theorem pointer (state : GlobalAddressState) (base : UInt64) (id : AllocId)
    (hooks : AddressLookupHooks) (position : Nat) (valid : position < state.intToPtrMap.size)
    (ordered : Ordered state.intToPtrMap) (row : state.intToPtrMap[position]? = some ⟨base,id⟩)
    (arithmetic : PointerArithmetic) (width : arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : state.provenanceMode ≠ .strict)
    (exposed : state.exposed.contains id = true) (live : hooks.isLive id = some true)
    (cached : state.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩) :
    state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes base)) 0 hooks arithmetic =
      .ok (some (id,Size.ZERO)) := by
  subst arithmetic
  unfold GlobalAddressState.ptrGetAlloc
  unfold_internal ".GlobalAddressState.findBase"
  simp only [Pointer.new,Size.ofBytes,allocation state base id hooks position valid ordered row mode exposed live,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,cached,Option.map_some,UInt64.sub_self]
  erw [DuplicatePrefix.PointerArithmetic.truncate_u64_identity]
  rfl

theorem resolve {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (base : UInt64) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (position : Nat)
    (valid : position < before.machine.user.addresses.intToPtrMap.size)
    (ordered : Ordered before.machine.user.addresses.intToPtrMap)
    (row : before.machine.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : before.machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : before.machine.user.addresses.exposed.contains id = true)
    (cached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes base)) before =
      .ok (some ⟨id,Size.ZERO,.wildcard⟩) before := by
  have member := Array.mem_of_find?_eq_some present
  have any : before.machine.memory.live.any (fun row => row.1 == id) = true :=
    Array.any_eq_true'.mpr ⟨(id,entry),member,by simp⟩
  have live : before.machine.memory.isAllocLive id = true := by simp [MemoryState.isAllocLive,any]
  have resolution := pointer before.machine.user.addresses base id
    (⟨fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size),
      fun id => some (before.machine.memory.isAllocLive id)⟩ : AddressLookupHooks)
    position valid ordered row pointers.arithmetic width mode exposed (by simp [live]) cached
  simp only [Pointer.new] at resolution
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,Pointer.new,resolution,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Id.run]

end DuplicatePrefix.WildcardOrderedHitAddress
