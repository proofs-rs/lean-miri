import duplicate_prefix.WildcardOrderedMissRetag
import duplicate_prefix.ZeroReferenceBorrow
namespace DuplicatePrefix.WildcardOrderedMissZeroBorrow
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows
open RootEmptyReferenceValidity
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem reborrow_from_fields {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance) (policy : RetagPolicy.NewPermission)
    (tag : BorTag) (state : ValidityMachine.State K U) (address : UInt64)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes address))
    (mode : state.machine.user.addresses.provenanceMode ≠ .strict)
    (miss : WildcardOrderedMissAddress.Miss state.machine.user.addresses address) :
    TypedRetag.reborrow h budget place Size.ZERO policy tag state = .ok (some .wildcard) state := by
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO state = .ok () state := by
    rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access place.mplace.ptr state
  have resolve : h.resolveAllocation place.mplace.ptr state = .ok none state := by
    rw [sources.resolve,pointer]
    exact WildcardOrderedMissAddress.resolve_miss pointers state address mode miss
  unfold TypedRetag.reborrow
  simp only [check,resolve,sources.log,bind,EStateM.bind,pure,EStateM.pure]
  simp [Size.ZERO,pointer,Pointer.new,bind,EStateM.bind,pure,EStateM.pure]

theorem zero_place_at {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (policy : RetagPolicy.NewPermission) (align : Align)
    (before : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (enabled : before.machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (wildcard : place.mplace.ptr.provenance = some .wildcard)
    (sizing : h.sizeAndAlign place before = .ok (some (Size.ZERO, align)) before)
    (reborrow : TypedRetag.reborrow h budget place Size.ZERO policy tracker.global.nextPointerTag
      (TypedRetagEmpty.afterTag before tracker fresh) =
      .ok (some .wildcard) (TypedRetagEmpty.afterTag before tracker fresh)) :
    TypedRetag.retagPlace h budget place policy before =
      .ok place (TypedRetagEmpty.afterTag before tracker fresh) := by
  unfold TypedRetag.retagPlace
  simp only [bind, EStateM.bind]
  rw [sizing]
  simp only [pure, EStateM.pure, Option.map_some, Option.getD_some]
  unfold_typed ".TypedRetag.tracker"
  unfold_typed ".TypedRetag.checked"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, enabled, TypedRetagEmpty.allocate_tag tracker.global fresh]
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    bind, EStateM.bind, pure, EStateM.pure]
  erw [reborrow]
  simp only [wildcard, bind, EStateM.bind, pure, EStateM.pure]
  simp only [← wildcard]

theorem pointer {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (reference pointee : LocalLayout) (address : UInt64)
    (mutability : Miri.MIR.Mutability) (retagMode : RetagPolicy.RetagMode) (policy : RetagPolicy.NewPermission)
    (shape : h.typeShape reference.ty = pure .reference)
    (pointeeQuery : h.referencePointee reference.ty = pure (pointee.ty,mutability))
    (unpin : h.isUnpin pointee.ty = pure true) (unsafeUnpin : h.isUnsafeUnpin pointee.ty = pure true)
    (frozen : h.typeIsFreeze pointee.ty = pure true)
    (created : RetagPolicy.create ⟨true,true,true⟩ (if mutability == .Mut then .Mutable else .Shared)
      retagMode ⟨false,false⟩ = some policy)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some pointee.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (pointeeAlign : pointee.layout.align.abi = Align.ONE)
    (width : access.runtime.base.pointerWidth = .w64)
    (state : ValidityMachine.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (frameShape : state.stack.frames = frames.push frame)
    (tracker : MachineHooks.BorrowState) (enabled : state.machine.borrowTracker = some tracker)
    (modeEq : tracker.retagMode = retagMode)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (addressMode : state.machine.user.addresses.provenanceMode ≠ .strict)
    (miss : WildcardOrderedMissAddress.Miss state.machine.user.addresses address)
    (sizingAt : h.sizeAndAlign (RetagReferencePlace.slicePlace (Pointer.new .wildcard (Size.ofBytes address)) 0 pointee) state =
      .ok (some (Size.ZERO, Align.ONE)) state) :
    TypedRetag.machineRetagPtrValue h budget (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference)
      reference.ty state = .ok (some (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference))
        (TypedRetagEmpty.afterTag state tracker fresh) := by
  let value := RetagReferencePlace.sliceValue access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference
  let place := RetagReferencePlace.slicePlace (Pointer.new .wildcard (Size.ofBytes address)) 0 pointee
  have construct : h.immPtrToMPlace value = pure place := by
    rw [sources.construct]
    exact RetagReferencePlace.canonical_from_immediate access prepared choice _ 0 reference pointee
      dereference pointeeLayout pointeeAlign
  have reborrow := reborrow_from_fields h prepared access projection vtable
    pointers choice sources budget place policy tracker.global.nextPointerTag
    (TypedRetagEmpty.afterTag state tracker fresh) address rfl addressMode miss
  have retag := zero_place_at h budget place policy
    Align.ONE state tracker enabled fresh rfl sizingAt reborrow
  have permission := TypedRetagPolicyFields.new_permission_general h pointee.ty
    (if mutability == .Mut then .Mutable else .Shared) retagMode state frames frame frameShape
    unpin unsafeUnpin frozen sources.implicitWrites
  rw [created] at permission
  have reconstruct : h.reconstruct value place = pure value := by
    rw [sources.reconstruct]
    funext after
    simp [TypedMachineBindings.retagHooks, value, place, RetagReferencePlace.slicePlace,
      RetagReferencePlace.sliceValue, MemPlace.toRef, Immediate.newPointerWithMeta,
      Pointer.withOptionalProvenance,Pointer.new,Scalar.fromMaybePointer,
      Except.mapError, Except.bind, Except.pure, bind, EStateM.bind, pure, EStateM.pure]
  have result := TypedBorrowSteps.reference_pointer_of_steps h budget value value place place pointee.ty mutability
    retagMode policy state (TypedRetagEmpty.afterTag state tracker fresh)
    shape pointeeQuery permission construct retag reconstruct
  unfold TypedRetag.machineRetagPtrValue
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, enabled, modeEq]
  exact result

end DuplicatePrefix.WildcardOrderedMissZeroBorrow
