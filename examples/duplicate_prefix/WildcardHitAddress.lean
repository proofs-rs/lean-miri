import duplicate_prefix.WildcardMissAddress
import duplicate_prefix.RetagPointerChecks

namespace DuplicatePrefix.WildcardHitAddress
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem allocation (state : GlobalAddressState) (base : UInt64) (id : AllocId)
    (hooks : AddressLookupHooks) (mode : state.provenanceMode ≠ .strict)
    (mapping : state.intToPtrMap = #[⟨base,id⟩])
    (exposed : state.exposed.contains id = true) (live : hooks.isLive id = some true) :
    state.allocIdFromAddr base 0 hooks = .ok (some id) := by
  have member : id ∈ state.exposed := by simpa using exposed
  have search := WildcardMissAddress.inverse_singleton base id
  unfold GlobalAddressState.allocIdFromAddr
  unfold_global_data ".GlobalAddressState.inverseSearch"
  simp [mode,mapping,search,member,live,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

theorem pointer (state : GlobalAddressState) (base : UInt64) (id : AllocId)
    (hooks : AddressLookupHooks) (arithmetic : PointerArithmetic)
    (width : arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : state.provenanceMode ≠ .strict)
    (mapping : state.intToPtrMap = #[⟨base,id⟩])
    (exposed : state.exposed.contains id = true) (live : hooks.isLive id = some true)
    (cached : state.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩) :
    state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes base)) 0 hooks arithmetic =
      .ok (some (id,Size.ZERO)) := by
  subst arithmetic
  unfold GlobalAddressState.ptrGetAlloc
  unfold_internal ".GlobalAddressState.findBase"
  simp only [Pointer.new,Size.ofBytes,allocation state base id hooks mode mapping exposed live,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure,cached,Option.map_some,UInt64.sub_self]
  erw [DuplicatePrefix.PointerArithmetic.truncate_u64_identity]
  rfl

/-- Exact-base exposed live hits derive real resolution from address/allocation
rows. Callback errors are not collapsed into successful unresolved results. -/
theorem resolve {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (base : UInt64) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : before.machine.user.addresses.provenanceMode ≠ .strict)
    (mapping : before.machine.user.addresses.intToPtrMap = #[⟨base,id⟩])
    (exposed : before.machine.user.addresses.exposed.contains id = true)
    (cached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes base)) before =
      .ok (some ⟨id,Size.ZERO,.wildcard⟩) before := by
  have member := Array.mem_of_find?_eq_some present
  have any : before.machine.memory.live.any (fun row => row.1 == id) = true := by
    exact Array.any_eq_true'.mpr ⟨(id,entry),member,by simp⟩
  have live : before.machine.memory.isAllocLive id = true := by
    simp [MemoryState.isAllocLive,any]
  have resolution := pointer before.machine.user.addresses base id
    (⟨fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size),
      fun id => some (before.machine.memory.isAllocLive id)⟩ : AddressLookupHooks)
    pointers.arithmetic width mode mapping exposed (by simp [live]) cached
  simp only [Pointer.new] at resolution
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,Pointer.new,resolution,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Id.run]
end DuplicatePrefix.WildcardHitAddress
