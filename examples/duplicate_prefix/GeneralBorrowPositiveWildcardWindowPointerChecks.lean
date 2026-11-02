import duplicate_prefix.GeneralBorrowPositiveWildcardPointerChecks
import duplicate_prefix.WildcardGeneralHitReborrow
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowPointerChecks
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefix.RetagPointerChecks
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Raw ordered inverse-address geometry derives either an exact-base hit or
an interior cut, including the true allocation-relative offset. -/
theorem geometry (entries : Array InverseAddressEntry) (base offset len : UInt64) (id : AllocId) (size : Size)
    (position : Nat) (valid : position<entries.size) (ordered : WildcardInteriorHitAddress.Ordered entries)
    (row : entries[position]?=some ⟨base,id⟩)
    (beforeNext : ∀nextValid:position+1<entries.size,base+offset<entries[position+1].address)
    (positive : (0 : UInt64)<len) (bounds : offset.toNat+len.toNat≤size.bytes.toNat)
    (pointerFits : base.toNat+offset.toNat+len.toNat<2^64) :
    WildcardGeneralHitReborrow.Geometry entries (base+offset) base id size := by
  by_cases zero : offset=0
  · left;exact ⟨by simp [zero],position,valid,ordered,row⟩
  · right
    have positiveOffset : 0<offset.toNat := by
      have nonzero : offset.toNat≠0 := by intro equal;exact zero (UInt64.toNat_inj.mp equal)
      omega
    have sum : (base+offset).toNat=base.toNat+offset.toNat := by
      simp only [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega : base.toNat+offset.toNat<2^64)]
    have afterBase : base<base+offset := UInt64.lt_iff_toNat_lt.mpr (by rw [sum];omega)
    have relative : (base+offset)-base=offset := by rw [UInt64.add_comm base offset,UInt64.add_sub_cancel]
    exact ⟨position,WildcardInteriorHitAddress.cut_of_ordered entries (base+offset) base id position valid ordered row afterBase beforeNext,
      row,by rw [relative];apply UInt64.lt_iff_toNat_lt.mpr;have h:=UInt64.lt_iff_toNat_lt.mp positive;omega⟩

/-- Positive signed sizes use the same source inverse search as size zero. -/
theorem pointer (state : GlobalAddressState) (address base : UInt64) (id : AllocId)
    (hooks : AddressLookupHooks) (capacity : Size)
    (geometry : WildcardGeneralHitReborrow.Geometry state.intToPtrMap address base id capacity)
    (arithmetic : PointerArithmetic) (width : arithmetic=⟨Size.ofBytes 8⟩)
    (mode : state.provenanceMode≠.strict) (exposed : state.exposed.contains id=true)
    (live : hooks.isLive id=some true)
    (cached : state.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩)
    (known : hooks.sizeOf id=some capacity) (size : Int64) (nonnegative : 0≤size.toInt) :
    state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) size hooks arithmetic=
      .ok (some (id,Size.ofBytes (address-base))) := by
  have original : state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0 hooks arithmetic=
      .ok (some (id,Size.ofBytes (address-base))) := by
    rcases geometry with ⟨same,position,valid,ordered,row⟩ | ⟨position,cut,row,inside⟩
    · subst address
      simpa only [UInt64.sub_self,Size.ZERO,Size.ofBytes] using WildcardOrderedHitAddress.pointer state base id hooks position valid ordered row arithmetic width mode exposed live cached
    · exact WildcardInteriorHitAddress.pointer state address base id hooks capacity position arithmetic width mode cut row known inside exposed live cached
  have alloc : state.allocIdFromAddr address size hooks=state.allocIdFromAddr address 0 hooks := by
    simp [GlobalAddressState.allocIdFromAddr,show ¬size.toInt<0 from by omega]
  unfold GlobalAddressState.ptrGetAlloc at original ⊢
  simpa only [Pointer.new,Size.ofBytes,alloc] using original

/-- Actual positive wildcard typed-memory resolution from raw ordered inverse
geometry, live/exposed membership and a cached base. -/
theorem resolve {K U : Type} (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (state : ValidityMachine.State K U) (base offset len : UInt64) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K)
    (geometry : WildcardGeneralHitReborrow.Geometry state.machine.user.addresses.intToPtrMap (base+offset) base id entry.allocation.byteSize)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : state.machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : state.machine.user.addresses.exposed.contains id = true)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (signedFits : len.toNat < 9223372036854775808) :
    TypedMemoryProviders.resolvePointer pointers state.machine.memory (Pointer.new (some Provenance.wildcard) (Size.ofBytes (base+offset)))
      (Int.ofNat len.toNat) state.machine = .ok (.ok ⟨id,(Size.ofBytes offset),.wildcard⟩) state.machine := by
  have member := Array.mem_of_find?_eq_some present
  have any : state.machine.memory.live.any (fun row => row.1 == id) = true := Array.any_eq_true'.mpr ⟨(id,entry),member,by simp⟩
  have live : state.machine.memory.isAllocLive id = true := by simp [MemoryState.isAllocLive,any]
  have signed : (Int64.ofInt (Int.ofNat len.toNat)).toInt = (len.toNat : Int) :=
    Int64.toInt_ofInt_of_le (Int.le_trans (by decide) (Int.natCast_nonneg _)) (Int.ofNat_lt.mpr signedFits)
  have resolution := pointer state.machine.user.addresses (base+offset) base id
    (⟨fun id => (state.machine.memory.getAllocInfo id).toOption.map (·.size),fun id => some (state.machine.memory.isAllocLive id)⟩ : AddressLookupHooks)
    entry.allocation.byteSize geometry pointers.arithmetic width mode exposed (by simp [live]) cached
    (WildcardGapAddress.size_of_live state.machine.memory id entry present) (Int64.ofInt (Int.ofNat len.toNat)) (by rw [signed];omega)
  have relative : (base+offset)-base=offset := by rw [UInt64.add_comm base offset,UInt64.add_sub_cancel]
  rw [relative] at resolution
  unfold TypedMemoryProviders.resolvePointer
  have lowerFalse : decide ((Int.ofNat len.toNat) < -(2^63 : Int)) = false := by simp <;> omega
  have upperFalse : decide ((Int.ofNat len.toNat) ≥ (2^63 : Int)) = false := by simp <;> omega
  simp only [Pointer.new,lowerFalse,upperFalse,Bool.false_or,Bool.false_eq_true,↓reduceIte,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  erw [resolution]
  rfl

private theorem pure_access {K : Type} (target : PointerArithmetic)
    (memory : MemoryState Provenance BorrowTree K) (base offset len : UInt64) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : 0 < len.toNat) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    checkPtrAccess target (Pointer.new (some Provenance.wildcard) (Size.ofBytes (base+offset))) (Size.ofBytes len) (.dereferenceable "pointer")
      (fun _ _ => .ok (⟨id,(Size.ofBytes offset),.wildcard⟩ : ResolvedPointer ProvenanceExtra)) memory.getAllocInfo = .ok () := by
  have signed := DuplicatePrefix.signed_size_ok (Size.ofBytes len) signedFits
  change sizeAsI64 (Size.ofBytes len) = .ok (Int.ofNat len.toNat) at signed
  have info := MemoryCopyBridge.live_alloc_info memory id entry present
  have dereferenced := PointerAccess.dereference_ok target (Pointer.new (some Provenance.wildcard) (Size.ofBytes (base+offset))) len.toNat (.dereferenceable "pointer")
    (fun _ _ => .ok (⟨id,(Size.ofBytes offset),.wildcard⟩ : ResolvedPointer ProvenanceExtra)) memory.getAllocInfo ⟨id,(Size.ofBytes offset),.wildcard⟩
    ⟨entry.allocation.byteSize,entry.allocation.align,.liveData,entry.allocation.mutability⟩
    positive signedFits rfl info (by simp) (by simpa [Size.ofBytes] using bounds)
  exact wildcard_pure_check_stage target _ _ _ _ _ _ _ signed dereferenced

/-- Positive physical wildcard pointer checking includes signed size, actual
resolver hit, allocation liveness and byte bounds. No checked-access result is
supplied as an input. -/
theorem check {K U : Type} (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (access : ValidityMachine.Access K U) (state : ValidityMachine.State K U) (base offset len : UInt64) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K)
    (geometry : WildcardGeneralHitReborrow.Geometry state.machine.user.addresses.intToPtrMap (base+offset) base id entry.allocation.byteSize)
    (wiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : state.machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : state.machine.user.addresses.exposed.contains id = true)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    ValidityMachine.checkPointerAccess access (Pointer.new (some Provenance.wildcard) (Size.ofBytes (base+offset))) (Size.ofBytes len) state = .ok () state := by
  let pointer := Pointer.new (some Provenance.wildcard) (Size.ofBytes (base+offset))
  let resolved : ResolvedPointer ProvenanceExtra := ⟨id,(Size.ofBytes offset),.wildcard⟩
  have actual := resolve pointers state base offset len id entry geometry width mode exposed cached present signedFits
  have resolution := wildcard_validity_resolve_stage access state pointer (Int.ofNat len.toNat) resolved
    (by rw [wiring];exact actual)
  have signed := DuplicatePrefix.signed_size_ok (Size.ofBytes len) signedFits
  change sizeAsI64 (Size.ofBytes len) = .ok (Int.ofNat len.toNat) at signed
  have positiveNat : 0 < len.toNat := by simpa only [UInt64.lt_iff_toNat_lt,UInt64.toNat_zero] using positive
  have checked := pure_access ⟨access.runtime.pointerSize⟩ state.machine.memory base offset len id entry present positiveNat signedFits bounds
  have nonzero : (Int.ofNat len.toNat == 0) = false := by simp <;> omega
  exact wildcard_validity_stage access state pointer (Size.ofBytes len) (Int.ofNat len.toNat) resolved
    signed nonzero resolution checked

end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowPointerChecks
