import duplicate_prefix.ConcreteEmptyReferenceBorrow
import duplicate_prefix.WildcardGeneralHitReborrow
import duplicate_prefix.GlobalAddressLiveErrorExclusion
namespace DuplicatePrefix.S03WildcardNonliveBorrow
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Input Miri.Interpreter
open Miri.Memory.AllocAddresses
open TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Exact-base and interior nonlive hits use the unchanged resolver.
Geometry and source metadata suffice; resolver success is derived. -/
theorem resolve {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (address base : UInt64) (id : AllocId) (info : AllocationInfo)
    (known : before.machine.memory.getAllocInfo id = .ok info)
    (geometry : WildcardGeneralHitReborrow.Geometry before.machine.user.addresses.intToPtrMap address base id info.size)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (mode : before.machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : before.machine.user.addresses.exposed.contains id = true)
    (cached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : before.machine.memory.isAllocLive id = true) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before =
      .ok (some ⟨id,Size.ofBytes (address-base),.wildcard⟩) before := by
  let hooks : AddressLookupHooks := GlobalAddressLiveErrorExclusion.lookup before.machine.memory
  have resolved : before.machine.user.addresses.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0 hooks pointers.arithmetic =
      .ok (some (id,Size.ofBytes (address-base))) := by
    rcases geometry with ⟨same,position,valid,ordered,row⟩ | ⟨position,cut,row,inside⟩
    · subst address
      simpa only [UInt64.sub_self,Size.ZERO,Size.ofBytes] using
        WildcardOrderedHitAddress.pointer before.machine.user.addresses base id hooks position valid ordered row
          pointers.arithmetic width mode exposed (by simp [hooks,GlobalAddressLiveErrorExclusion.lookup,live]) cached
    · exact WildcardInteriorHitAddress.pointer before.machine.user.addresses address base id hooks info.size position
        pointers.arithmetic width mode cut row (by change (before.machine.memory.getAllocInfo id).toOption.map (·.size) = some info.size;rw [known];rfl) inside exposed
        (by simp [hooks,GlobalAddressLiveErrorExclusion.lookup,live]) cached
  dsimp only [hooks,GlobalAddressLiveErrorExclusion.lookup] at resolved
  simp only [Pointer.new] at resolved
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,Pointer.new,resolved,
    hooks,GlobalAddressLiveErrorExclusion.lookup,get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Id.run]

theorem nonlive_zero_reference_pointer {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId)
    (base offset : UInt64) (tag : BorTag)
    (tagEq : tag = tracker.global.nextPointerTag)
    (policy : RetagPolicy.NewPermission)
    (protection : policy.protector = some .StrongProtector)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes (base+offset)))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (nonstrict : machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (live : machine.memory.isAllocLive id = true)
    (info : AllocationInfo)
    (metadata : machine.memory.getAllocInfo id = .ok info)
    (nonlive : info.kind ≠ .liveData)
    (geometry : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap (base+offset) base id info.size)
    (reference : LocalLayout) (mutability : Miri.MIR.Mutability) (mode : RetagPolicy.RetagMode)
    (created : RetagPolicy.create ⟨true,true,true⟩ (if mutability == .Mut then .Mutable else .Shared)
      mode ⟨false,false⟩ = some policy)
    (shape : h.typeShape reference.ty = pure .reference)
    (pointeeQuery : h.referencePointee reference.ty = pure (place.layout.ty,mutability))
    (unpin : h.isUnpin place.layout.ty = pure true)
    (unsafeUnpin : h.isUnsafeUnpin place.layout.ty = pure true)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some place.layout.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context place.layout.ty = .ok place.layout)
    (pointeeAlign : place.layout.layout.align.abi = Align.ONE)
    (placeShape : place = RetagReferencePlace.slicePlace
      (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 place.layout)
    (sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes 0,Align.ONE)) (Storage.withCurrent frames frame machine)) :
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 reference)
      reference.ty mode (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))) 0 reference))
      (Storage.withCurrent frames (TypedBorrowSteps.registeredFrame frame borrowFrame id tag)
        (TypedBorrowSteps.registeredMachine (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) tag)) := by
  subst tag
  let before := Storage.withCurrent frames frame machine
  let after := Storage.withCurrent frames (TypedBorrowSteps.registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
    (TypedBorrowSteps.registeredMachine (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) tracker.global.nextPointerTag)
  let oldPointer := Pointer.new Provenance.wildcard (Size.ofBytes (base+offset))
  let newPointer := Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer 0 reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer 0 reference
  let allocated := allocatedMachine machine tracker fresh
  let allocatedBorrow := allocatedTracker tracker fresh
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO (Storage.withCurrent frames frame allocated) =
      .ok () (Storage.withCurrent frames frame allocated) := by
    rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access place.mplace.ptr _
  have resolve : h.resolveAllocation place.mplace.ptr (Storage.withCurrent frames frame allocated) =
      .ok (some ⟨id, Size.ofBytes offset, .wildcard⟩) (Storage.withCurrent frames frame allocated) := by
    rw [sources.resolve, pointer]
    have result := S03WildcardNonliveBorrow.resolve pointers (Storage.withCurrent frames frame allocated)
      (base+offset) base id info metadata geometry width nonstrict exposed cached live
    have difference : base+offset-base = offset := by rw [UInt64.add_comm];exact UInt64.add_sub_cancel _ _
    simpa only [difference] using result
  have reborrow := TypedBorrowSteps.protected_nonlive_zero_of_metadata h budget place frames frame borrowFrame
    allocated allocatedBorrow rfl frameBorrow id offset .wildcard tracker.global.nextPointerTag
    policy protection info metadata nonlive check resolve (by rw [sources.log])
  have retag := TypedBorrowSteps.retag_place_at_of_reborrow h budget place policy (Size.ofBytes 0) Align.ONE
    before after tracker enabled fresh id .wildcard (by rw [pointer]; rfl) sizing reborrow
  have permission := TypedRetagPolicyFields.new_permission_general h place.layout.ty
    (if mutability == .Mut then .Mutable else .Shared) mode before frames frame rfl
    unpin unsafeUnpin frozen sources.implicitWrites
  rw [created] at permission
  have construct : h.immPtrToMPlace value = pure place := by
    rw [sources.construct]
    exact Eq.trans (RetagReferencePlace.canonical_from_immediate access prepared choice oldPointer 0 reference
      place.layout dereference pointeeLayout pointeeAlign) (congrArg pure placeShape.symm)
  have changed : TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag =
      RetagReferencePlace.slicePlace newPointer 0 place.layout := by rw [placeShape]; rfl
  have reconstruct : h.reconstruct value (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) = pure output := by
    rw [sources.reconstruct, changed]
    exact RetagReferencePlace.bound_reconstruct access h value newPointer 0 place.layout
  exact TypedBorrowSteps.reference_pointer_of_steps h budget value output place
    (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) place.layout.ty mutability mode policy
    before after shape pointeeQuery permission construct retag reconstruct

end DuplicatePrefix.S03WildcardNonliveBorrow
