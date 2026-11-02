import duplicate_prefix.GeneralRangeMapFind
import duplicate_prefix.GlobalDataOnlyConversion
import Miri.Interpreter.TypedValidityProviders
import Miri.Interpreter.PointerSource
namespace DuplicatePrefix.WildcardMissAddress
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

open Lean Elab in
elab "miss_source_inverse_search" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".findInverseIndex" then some name else none
  let [name] := names | throwError "expected original inverse-address search"
  Lean.Meta.mkConstWithFreshMVarLevels name

/-- Addresses below every inverse-map entry genuinely miss the actual binary
search, for arbitrary map length; no resolver-success premise is supplied. -/
theorem inverse_below (entries : Array InverseAddressEntry) (address : UInt64)
    (below : ∀ entry ∈ entries, address < entry.address) :
    miss_source_inverse_search entries address = (0,false) := by
  unfold_global_data ".findInverseIndex"
  simp only [Id.run,bind,pure,Id.instMonad,ForIn.forIn]
  name_range_scan
  let invariant : (Nat × Nat × Option Nat) → Prop := fun state =>
    state.1=0 ∧ state.2.1≤entries.size ∧ state.2.2=none
  let finished : (Nat × Nat × Option Nat) → Prop := fun state => state.1=0 ∧ state.2.2=none
  have step : ∀ state, invariant state →
      (∃ done, scan () state = .done done ∧ finished done) ∨
      ∃ next, scan () state = .yield next ∧ invariant next ∧ next.2.1<state.2.1 := by
    intro state valid
    rcases state with ⟨low,high,found⟩
    rcases valid with ⟨zero,bound,missing⟩
    change low=0 at zero
    change high≤entries.size at bound
    change found=none at missing
    subst low
    subst found
    by_cases empty : high=0
    · subst high
      exact .inl ⟨(0,0,none),by simp [scan],rfl,rfl⟩
    · have midpoint : high/2<high := by omega
      have validMiddle : high/2<entries.size := by omega
      have above := below entries[high/2] (Array.getElem_mem validMiddle)
      have notBefore : ¬entries[high/2].address<address := by
        have aboveNat := UInt64.lt_iff_toNat_lt.mp above
        intro contrary
        have contraryNat := UInt64.lt_iff_toNat_lt.mp contrary
        omega
      refine .inr ⟨(0,high/2,none),?_,?_,midpoint⟩
      · simp [scan,empty,validMiddle,above,notBefore]
      · refine ⟨rfl,?_,rfl⟩
        change high/2≤entries.size
        omega
  have final := GeneralRangeMapFind.loop_finished scan (fun state => state.2.1) invariant finished step
    (0,entries.size,none) ⟨rfl,Nat.le_refl _,rfl⟩
  simp only [finished] at final
  simp [final.1,final.2]

/-- Address-only data ensuring resolution remains absent: either the original
below-all case, or a singleton exact inverse-map base whose allocation is NOT
exposed. The latter actually finds the row and then takes exposure rejection;
no size/liveness or successful-lookup premise is supplied. -/
def Miss (state : GlobalAddressState) (address : UInt64) : Prop :=
  (∀ entry ∈ state.intToPtrMap, address < entry.address) ∨
  ∃ id, state.intToPtrMap = #[⟨address,id⟩] ∧ state.exposed.contains id = false

/-- The source binary search genuinely finds a singleton exact address. -/
theorem inverse_singleton (address : UInt64) (id : AllocId) :
    miss_source_inverse_search #[⟨address,id⟩] address = (0,true) := by
  unfold_global_data ".findInverseIndex"
  simp only [Id.run,bind,pure,Id.instMonad,ForIn.forIn]
  name_range_scan
  have noLt : ¬ address < address := by simp
  let initial : Nat × Nat × Option Nat := (0,1,none)
  let found : Nat × Nat × Option Nat := (0,1,some 0)
  let invariant := fun state => state = initial ∨ state = found
  let final := fun state => state = found
  let measure := fun state : Nat × Nat × Option Nat => if state.2.2.isNone then 1 else 0
  have step : ∀ state, invariant state →
      (∃ done, scan () state = .done done ∧ final done) ∨
      ∃ next, scan () state = .yield next ∧ invariant next ∧ measure next < measure state := by
    intro state valid
    rcases valid with rfl | rfl
    · exact Or.inr ⟨found,by simp [scan,initial,found,noLt],Or.inr rfl,by decide⟩
    · exact Or.inl ⟨found,by simp [scan,found],rfl⟩
  have finished := GeneralRangeMapFind.loop_finished scan measure invariant final step initial (Or.inl rfl)
  change (Lean.Loop.forIn {} initial scan) = found at finished
  simp only [Array.size_singleton,show (0,1,none) = initial from rfl,finished]
  rfl

/-- Both address-data miss cases resolve to none in default/permissive mode.
The exact unexposed-base branch skips allocation-size and liveness callbacks. -/
theorem allocation_miss (state : GlobalAddressState) (address : UInt64) (hooks : AddressLookupHooks)
    (mode : state.provenanceMode ≠ .strict) (miss : Miss state address) :
    state.allocIdFromAddr address 0 hooks = .ok none := by
  rcases miss with before | ⟨id,mapping,unexposed⟩
  · have search := inverse_below state.intToPtrMap address before
    unfold GlobalAddressState.allocIdFromAddr
    unfold_global_data ".GlobalAddressState.inverseSearch"
    simp [mode,search,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  · have notexposed : id ∉ state.exposed := by simpa using unexposed
    have search := inverse_singleton address id
    unfold GlobalAddressState.allocIdFromAddr
    unfold_global_data ".GlobalAddressState.inverseSearch"
    simp [mode,mapping,search,notexposed,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

/-- Strict provenance rejects even a zero-sized wildcard allocation lookup.
This is an address-policy error, not a successful unresolved-pointer result. -/
theorem allocation_strict (state : GlobalAddressState) (address : UInt64) (hooks : AddressLookupHooks)
    (mode : state.provenanceMode = .strict) :
    state.allocIdFromAddr address 0 hooks = .error .strictAddressLookup := by
  unfold GlobalAddressState.allocIdFromAddr
  simp only [mode,beq_self_eq_true,↓reduceIte]
  rfl

/-- The direct source address-error classifier calls strict lookup a machine
stop, rather than Rust UB or an unsupported operation. -/
theorem strict_classification : PointerSource.addressError .strictAddressLookup =
    .machineStop "Int2PtrWithStrictProvenance" := rfl

theorem pointer_miss (state : GlobalAddressState) (address : UInt64) (hooks : AddressLookupHooks)
    (arithmetic : PointerArithmetic) (mode : state.provenanceMode ≠ .strict)
    (miss : Miss state address) :
    state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0 hooks arithmetic = .ok none := by
  simp only [GlobalAddressState.ptrGetAlloc,Pointer.new,Size.ofBytes,allocation_miss state address hooks mode miss,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

/-- The real typed-retag resolver preserves an unresolved wildcard pointer's
state. Its zero-sized check does not skip this resolution operation. -/
theorem resolve_miss {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (address : UInt64)
    (mode : before.machine.user.addresses.provenanceMode ≠ .strict)
    (miss : Miss before.machine.user.addresses address) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before =
      .ok none before := by
  have resolution := pointer_miss before.machine.user.addresses address
    (⟨fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size),
      fun id => some (before.machine.memory.isAllocLive id)⟩ : AddressLookupHooks)
    pointers.arithmetic mode miss
  simp only [Pointer.new] at resolution
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,Pointer.new,resolution,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Id.run]
/-- The actual typed resolver reports strict wildcard lookup through its
callback-error path, rather than silently returning an unresolved pointer. -/
theorem resolve_strict {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (address : UInt64)
    (mode : before.machine.user.addresses.provenanceMode = .strict) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before =
      .error (.callback s!"address resolver: {reprStr AddressStateError.strictAddressLookup}") before := by
  have resolution : before.machine.user.addresses.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0
      (⟨fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size),
        fun id => some (before.machine.memory.isAllocLive id)⟩ : AddressLookupHooks)
      pointers.arithmetic = .error .strictAddressLookup := by
    simp only [GlobalAddressState.ptrGetAlloc,Pointer.new,Size.ofBytes,allocation_strict _ address _ mode,
      bind,Bind.bind,Except.bind]
  simp only [Pointer.new] at resolution
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,Pointer.new,resolution,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Id.run]
  rfl

end DuplicatePrefix.WildcardMissAddress
