import duplicate_prefix.GeneralRangeMapFind
import duplicate_prefix.GlobalDataOnlyConversion
import Miri.Interpreter.TypedValidityProviders
namespace DuplicatePrefix.WildcardEmptyAddress
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

open Lean Elab in
elab "source_inverse_search" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".findInverseIndex" then some name else none
  let [name] := names | throwError "expected original inverse-address search"
  Lean.Meta.mkConstWithFreshMVarLevels name

/-- Addresses below every inverse-map entry genuinely miss the actual binary
search, for arbitrary map length; no resolver-success premise is supplied. -/
theorem inverse_below (entries : Array InverseAddressEntry) (address : UInt64)
    (below : ∀ entry ∈ entries, address < entry.address) :
    source_inverse_search entries address = (0,false) := by
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

/-- Default/permissive wildcard lookup below the inverse map does not consult
allocation metadata, exposure membership or liveness. Strict mode is excluded. -/
theorem allocation_below (state : GlobalAddressState) (address : UInt64) (hooks : AddressLookupHooks)
    (mode : state.provenanceMode ≠ .strict)
    (below : ∀ entry ∈ state.intToPtrMap, address < entry.address) :
    state.allocIdFromAddr address 0 hooks = .ok none := by
  have search := inverse_below state.intToPtrMap address below
  unfold GlobalAddressState.allocIdFromAddr
  unfold_global_data ".GlobalAddressState.inverseSearch"
  simp [mode,search,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

theorem pointer_below (state : GlobalAddressState) (address : UInt64) (hooks : AddressLookupHooks)
    (arithmetic : PointerArithmetic) (mode : state.provenanceMode ≠ .strict)
    (below : ∀ entry ∈ state.intToPtrMap, address < entry.address) :
    state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0 hooks arithmetic = .ok none := by
  simp only [GlobalAddressState.ptrGetAlloc,Pointer.new,Size.ofBytes,allocation_below state address hooks mode below,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

/-- The real typed-retag resolver preserves an unresolved wildcard pointer's
state. Its zero-sized check does not skip this resolution operation. -/
theorem resolve_below {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (address : UInt64)
    (mode : before.machine.user.addresses.provenanceMode ≠ .strict)
    (below : ∀ entry ∈ before.machine.user.addresses.intToPtrMap, address < entry.address) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before =
      .ok none before := by
  have resolution := pointer_below before.machine.user.addresses address
    (⟨fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size),
      fun id => some (before.machine.memory.isAllocLive id)⟩ : AddressLookupHooks)
    pointers.arithmetic mode below
  simp only [Pointer.new] at resolution
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,Pointer.new,resolution,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Id.run]
end DuplicatePrefix.WildcardEmptyAddress
