import duplicate_prefix.WildcardOrderedHitAddress
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardPointerChecks
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefix.RetagPointerChecks
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

open Lean Elab in
elab "wildcard_validity_stage" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".RetagPointerChecks.check_pointer_stage" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected unique source-bound pointer check stage"
open Lean Elab in
elab "wildcard_validity_resolve_stage" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".RetagPointerChecks.validity_resolve_of_exact" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected unique source-bound validity resolver stage"

open Lean Elab in
elab "wildcard_pure_check_stage" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".RetagPointerChecks.pure_check_stage" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected unique source-bound pure pointer check stage"

/-- Positive signed sizes search the same exact-base inverse row as zero;
this is derived from the source search-address rule, not a resolver premise. -/
theorem pointer (state : GlobalAddressState) (base : UInt64) (id : AllocId)
    (hooks : AddressLookupHooks) (position : Nat) (valid : position < state.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered state.intToPtrMap)
    (row : state.intToPtrMap[position]? = some ⟨base,id⟩)
    (arithmetic : PointerArithmetic) (width : arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : state.provenanceMode ≠ .strict) (exposed : state.exposed.contains id = true)
    (live : hooks.isLive id = some true)
    (cached : state.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (size : Int64) (nonnegative : 0 ≤ size.toInt) :
    state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes base)) size hooks arithmetic = .ok (some (id,Size.ZERO)) := by
  have alloc : state.allocIdFromAddr base size hooks = state.allocIdFromAddr base 0 hooks := by
    simp [GlobalAddressState.allocIdFromAddr,show ¬size.toInt < 0 from by omega]
  have original := WildcardOrderedHitAddress.pointer state base id hooks position valid ordered row arithmetic width mode exposed live cached
  unfold GlobalAddressState.ptrGetAlloc at original ⊢
  simpa only [Pointer.new,Size.ofBytes,alloc] using original

/-- Actual positive wildcard typed-memory resolution from raw ordered inverse
geometry, live/exposed membership and a cached base. -/
theorem resolve {K U : Type} (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (state : ValidityMachine.State K U) (base len : UInt64) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K)
    (position : Nat) (valid : position < state.machine.user.addresses.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered state.machine.user.addresses.intToPtrMap)
    (row : state.machine.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : state.machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : state.machine.user.addresses.exposed.contains id = true)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (signedFits : len.toNat < 9223372036854775808) :
    TypedMemoryProviders.resolvePointer pointers state.machine.memory (Pointer.new (some Provenance.wildcard) (Size.ofBytes base))
      (Int.ofNat len.toNat) state.machine = .ok (.ok ⟨id,Size.ZERO,.wildcard⟩) state.machine := by
  have member := Array.mem_of_find?_eq_some present
  have any : state.machine.memory.live.any (fun row => row.1 == id) = true := Array.any_eq_true'.mpr ⟨(id,entry),member,by simp⟩
  have live : state.machine.memory.isAllocLive id = true := by simp [MemoryState.isAllocLive,any]
  have signed : (Int64.ofInt (Int.ofNat len.toNat)).toInt = (len.toNat : Int) :=
    Int64.toInt_ofInt_of_le (Int.le_trans (by decide) (Int.natCast_nonneg _)) (Int.ofNat_lt.mpr signedFits)
  have resolution := pointer state.machine.user.addresses base id
    (⟨fun id => (state.machine.memory.getAllocInfo id).toOption.map (·.size),fun id => some (state.machine.memory.isAllocLive id)⟩ : AddressLookupHooks)
    position valid ordered row pointers.arithmetic width mode exposed (by simp [live]) cached (Int64.ofInt (Int.ofNat len.toNat))
    (by rw [signed];omega)
  unfold TypedMemoryProviders.resolvePointer
  have lowerFalse : decide ((Int.ofNat len.toNat) < -(2^63 : Int)) = false := by simp <;> omega
  have upperFalse : decide ((Int.ofNat len.toNat) ≥ (2^63 : Int)) = false := by simp <;> omega
  simp only [Pointer.new,lowerFalse,upperFalse,Bool.false_or,Bool.false_eq_true,↓reduceIte,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  erw [resolution]
  rfl

private theorem pure_access {K : Type} (target : PointerArithmetic)
    (memory : MemoryState Provenance BorrowTree K) (base len : UInt64) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : 0 < len.toNat) (signedFits : len.toNat < 9223372036854775808)
    (bounds : len.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    checkPtrAccess target (Pointer.new (some Provenance.wildcard) (Size.ofBytes base)) (Size.ofBytes len) (.dereferenceable "pointer")
      (fun _ _ => .ok (⟨id,Size.ZERO,.wildcard⟩ : ResolvedPointer ProvenanceExtra)) memory.getAllocInfo = .ok () := by
  have signed := DuplicatePrefix.signed_size_ok (Size.ofBytes len) signedFits
  change sizeAsI64 (Size.ofBytes len) = .ok (Int.ofNat len.toNat) at signed
  have info := MemoryCopyBridge.live_alloc_info memory id entry present
  have dereferenced := PointerAccess.dereference_ok target (Pointer.new (some Provenance.wildcard) (Size.ofBytes base)) len.toNat (.dereferenceable "pointer")
    (fun _ _ => .ok (⟨id,Size.ZERO,.wildcard⟩ : ResolvedPointer ProvenanceExtra)) memory.getAllocInfo ⟨id,Size.ZERO,.wildcard⟩
    ⟨entry.allocation.byteSize,entry.allocation.align,.liveData,entry.allocation.mutability⟩
    positive signedFits rfl info (by simp) (by simpa [Size.ZERO] using bounds)
  exact wildcard_pure_check_stage target _ _ _ _ _ _ _ signed dereferenced

/-- Positive physical wildcard pointer checking includes signed size, actual
resolver hit, allocation liveness and byte bounds. No checked-access result is
supplied as an input. -/
theorem check {K U : Type} (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (access : ValidityMachine.Access K U) (state : ValidityMachine.State K U) (base len : UInt64) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K)
    (position : Nat) (valid : position < state.machine.user.addresses.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered state.machine.user.addresses.intToPtrMap)
    (row : state.machine.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (wiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : state.machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : state.machine.user.addresses.exposed.contains id = true)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : len.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    ValidityMachine.checkPointerAccess access (Pointer.new (some Provenance.wildcard) (Size.ofBytes base)) (Size.ofBytes len) state = .ok () state := by
  let pointer := Pointer.new (some Provenance.wildcard) (Size.ofBytes base)
  let resolved : ResolvedPointer ProvenanceExtra := ⟨id,Size.ZERO,.wildcard⟩
  have actual := resolve pointers state base len id entry position valid ordered row width mode exposed cached present signedFits
  have resolution := wildcard_validity_resolve_stage access state pointer (Int.ofNat len.toNat) resolved
    (by rw [wiring];exact actual)
  have signed := DuplicatePrefix.signed_size_ok (Size.ofBytes len) signedFits
  change sizeAsI64 (Size.ofBytes len) = .ok (Int.ofNat len.toNat) at signed
  have positiveNat : 0 < len.toNat := by simpa only [UInt64.lt_iff_toNat_lt,UInt64.toNat_zero] using positive
  have checked := pure_access ⟨access.runtime.pointerSize⟩ state.machine.memory base len id entry present positiveNat signedFits bounds
  have nonzero : (Int.ofNat len.toNat == 0) = false := by simp <;> omega
  exact wildcard_validity_stage access state pointer (Size.ofBytes len) (Int.ofNat len.toNat) resolved
    signed nonzero resolution checked

end DuplicatePrefix.GeneralBorrowPositiveWildcardPointerChecks
