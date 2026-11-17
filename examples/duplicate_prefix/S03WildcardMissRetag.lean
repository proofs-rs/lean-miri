import duplicate_prefix.WildcardZeroBorrow
import duplicate_prefix.GlobalAddressLiveErrorExclusion

namespace DuplicatePrefix.S03WildcardMissRetag
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Lift the miss returned by Candidate classification into the actual typed
allocation resolver. This covers every miss, including unexposed exact rows
and predecessor gaps; no below-all-rows restriction is introduced. -/
theorem resolve {K U : Type} (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (state : ValidityMachine.State K U) (address : UInt64)
    (miss : state.machine.user.addresses.allocIdFromAddr address 0
      (GlobalAddressLiveErrorExclusion.lookup state.machine.memory) = .ok none) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) state =
      .ok none state := by
  have pointer : state.machine.user.addresses.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0
      (GlobalAddressLiveErrorExclusion.lookup state.machine.memory) pointers.arithmetic = .ok none := by
    simp only [AllocAddresses.GlobalAddressState.ptrGetAlloc,Pointer.new,Size.ofBytes,miss,
      bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  simp only [Pointer.new] at pointer
  dsimp only [GlobalAddressLiveErrorExclusion.lookup] at pointer
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,Pointer.new,pointer,
    GlobalAddressLiveErrorExclusion.lookup,get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Id.run]

/-- The real unresolved zero-byte reborrow. Its initial lookup equation is
provided by Candidate classification at the enclosing dispatcher. -/
theorem reborrow {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance) (policy : RetagPolicy.NewPermission)
    (tag : BorTag) (state : ValidityMachine.State K U) (address : UInt64)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes address))
    (miss : state.machine.user.addresses.allocIdFromAddr address 0
      (GlobalAddressLiveErrorExclusion.lookup state.machine.memory) = .ok none) :
    TypedRetag.reborrow h budget place Size.ZERO policy tag state = .ok (some .wildcard) state := by
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO state = .ok () state := by
    rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access place.mplace.ptr state
  have resolved : h.resolveAllocation place.mplace.ptr state = .ok none state := by
    rw [sources.resolve,pointer]
    exact resolve pointers state address miss
  unfold TypedRetag.reborrow
  simp only [check,resolved,sources.log,bind,EStateM.bind,pure,EStateM.pure]
  simp [Size.ZERO,pointer,Pointer.new,bind,EStateM.bind,pure,EStateM.pure]

/-- Actual fresh-tag allocation followed by the generic no-location reborrow:
no protector/tree is fabricated, and original wildcard provenance is retained. -/
theorem retag_place {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance) (policy : RetagPolicy.NewPermission)
    (state : ValidityMachine.State K U) (tracker : MachineHooks.BorrowState)
    (enabled : state.machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (address : UInt64) (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes address))
    (sizing : h.sizeAndAlign place state = .ok (some (Size.ZERO,Align.ONE)) state)
    (miss : state.machine.user.addresses.allocIdFromAddr address 0
      (GlobalAddressLiveErrorExclusion.lookup state.machine.memory) = .ok none) :
    TypedRetag.retagPlace h budget place policy state = .ok place (TypedRetagEmpty.afterTag state tracker fresh) :=
  WildcardZeroBorrow.zero_place_at h budget place policy Align.ONE state tracker enabled fresh (by rw [pointer];rfl) sizing
    (reborrow h prepared access projection vtable pointers choice sources budget place policy tracker.global.nextPointerTag
      (TypedRetagEmpty.afterTag state tracker fresh) address pointer miss)

end DuplicatePrefix.S03WildcardMissRetag
