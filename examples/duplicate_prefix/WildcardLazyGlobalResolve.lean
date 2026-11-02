import duplicate_prefix.WildcardNonliveReferenceBorrow
import duplicate_prefix.WildcardGeneralHitReborrow
namespace DuplicatePrefix.WildcardLazyGlobalResolve
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Cold live-data globals resolve from their STORED size metadata and cached
address, before get_alloc_extra materializes any local allocation. -/
theorem resolve {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (address base : UInt64) (id : AllocId)
    (size : Size) (geometry : WildcardGeneralHitReborrow.Geometry before.machine.user.addresses.intToPtrMap address base id size)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : before.machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : before.machine.user.addresses.exposed.contains id = true)
    (cached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : before.machine.memory.isAllocLive id = true)
    (known : (before.machine.memory.getAllocInfo id).toOption.map (·.size) = some size) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before =
      .ok (some ⟨id,Size.ofBytes (address-base),.wildcard⟩) before := by
  have resolution : before.machine.user.addresses.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0
      (⟨fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size),
        fun id => some (before.machine.memory.isAllocLive id)⟩ : AddressLookupHooks) pointers.arithmetic =
      .ok (some (id,Size.ofBytes (address-base))) := by
    rcases geometry with ⟨same,position,valid,ordered,row⟩ | ⟨position,cut,row,inside⟩
    · subst address
      simpa only [UInt64.sub_self,Size.ZERO,Size.ofBytes] using
        WildcardOrderedHitAddress.pointer before.machine.user.addresses base id _ position valid ordered row
          pointers.arithmetic width mode exposed (by simp [live]) cached
    · exact WildcardInteriorHitAddress.pointer before.machine.user.addresses address base id _ size position
        pointers.arithmetic width mode cut row known inside exposed (by simp [live]) cached
  simp only [Pointer.new] at resolution
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,Pointer.new,resolution,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Id.run]
end DuplicatePrefix.WildcardLazyGlobalResolve
