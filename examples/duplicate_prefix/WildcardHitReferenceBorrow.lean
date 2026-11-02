import duplicate_prefix.WildcardHitProtectedReborrow
namespace DuplicatePrefix.WildcardHitReferenceBorrow
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Input Miri.Interpreter
open TypedBorrowSteps ReferenceBorrowDriver
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem pointer_append {K U C F A : Type} [DecidableEq K]
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
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (base : UInt64) (tag : BorTag)
    (tagEq : tag = tracker.global.nextPointerTag)
    (initial : Tree.LocationState) (policy : RetagPolicy.NewPermission)
    (protection : policy.protector = some .StrongProtector)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (initialState : RetagPolicy.initialLocationState policy true = .ok initial)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes base))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (inverse : machine.user.addresses.intToPtrMap = #[⟨base,id⟩])
    (exposed : machine.user.addresses.exposed.contains id = true)
    (tagMapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (sifa : IdempotentForeignAccess)
    (outsideInitial : policy.outsidePermission.isInitial = true)
    (outsideNonunique : policy.outsidePermission.isUnique = false)
    (foreign : policy.outsidePermission.strongestIdempotentForeignAccess policy.protector.isSome = .Access sifa)
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
      (Pointer.new .wildcard (Size.ofBytes base)) 0 place.layout)
    (sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes 0,Align.ONE)) (Storage.withCurrent frames frame machine)) :
    let finalTree := WildcardHitZeroConstructor.installed entry.allocation.extra
      ⟨entry.allocation.extra.tagMapping.mapping.push (tracker.global.nextPointerTag,
        ⟨UInt32.ofNat entry.allocation.extra.tagMapping.mapping.size⟩),entry.allocation.extra.tagMapping.deassigned⟩
      ⟨UInt32.ofNat entry.allocation.extra.tagMapping.mapping.size⟩ tracker.global.nextPointerTag policy.outsidePermission sifa
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes base)) 0 reference)
      reference.ty mode (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes base)) 0 reference))
      (Storage.withCurrent frames (TypedBorrowSteps.registeredFrame frame borrowFrame id tag)
        {TypedBorrowSteps.registeredMachine (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) tag
          with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}) := by
  subst tag
  dsimp only
  let finalTree := WildcardHitZeroConstructor.installed entry.allocation.extra
      ⟨entry.allocation.extra.tagMapping.mapping.push (tracker.global.nextPointerTag,
        ⟨UInt32.ofNat entry.allocation.extra.tagMapping.mapping.size⟩),entry.allocation.extra.tagMapping.deassigned⟩
      ⟨UInt32.ofNat entry.allocation.extra.tagMapping.mapping.size⟩ tracker.global.nextPointerTag policy.outsidePermission sifa
  let before := Storage.withCurrent frames frame machine
  let after := Storage.withCurrent frames (TypedBorrowSteps.registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
    {TypedBorrowSteps.registeredMachine (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) tracker.global.nextPointerTag
      with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
  let oldPointer := Pointer.new (Provenance.wildcard) (Size.ofBytes base)
  let newPointer := Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes base)
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer 0 reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer 0 reference
  let allocated := allocatedMachine machine tracker fresh
  let allocatedBorrow := allocatedTracker tracker fresh
  have reborrow := WildcardHitProtectedReborrow.append h prepared access projection vtable pointers choice sources
    budget place frames frame borrowFrame allocated allocatedBorrow rfl frameBorrow base id entry
    tracker.global.nextPointerTag policy initial protection frozen initialState pointer width addressMode inverse exposed cached present
    globalKind globals extraWiring synchronize tagMapFresh noFree fits sifa outsideInitial outsideNonunique foreign
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

theorem fnentry_pointer_append {K U C F A : Type} [DecidableEq K]
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
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (base : UInt64) (tag : BorTag)
    (tagEq : tag = tracker.global.nextPointerTag)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes base))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (inverse : machine.user.addresses.intToPtrMap = #[⟨base,id⟩])
    (exposed : machine.user.addresses.exposed.contains id = true)
    (tagMapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (reference : LocalLayout)
    (shape : h.typeShape reference.ty = pure .reference)
    (pointeeQuery : h.referencePointee reference.ty = pure (place.layout.ty,.Mut))
    (unpin : h.isUnpin place.layout.ty = pure true)
    (unsafeUnpin : h.isUnsafeUnpin place.layout.ty = pure true)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some place.layout.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context place.layout.ty = .ok place.layout)
    (pointeeAlign : place.layout.layout.align.abi = Align.ONE)
    (placeShape : place = RetagReferencePlace.slicePlace
      (Pointer.new .wildcard (Size.ofBytes base)) 0 place.layout)
    (sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes 0,Align.ONE)) (Storage.withCurrent frames frame machine)) :
    let finalTree := WildcardHitZeroConstructor.installed entry.allocation.extra
      ⟨entry.allocation.extra.tagMapping.mapping.push (tracker.global.nextPointerTag,
        ⟨UInt32.ofNat entry.allocation.extra.tagMapping.mapping.size⟩),entry.allocation.extra.tagMapping.deassigned⟩
      ⟨UInt32.ofNat entry.allocation.extra.tagMapping.mapping.size⟩ tracker.global.nextPointerTag ChildBorrow.fnEntryPolicy.outsidePermission .None
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes base)) 0 reference)
      reference.ty .FnEntry (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes base)) 0 reference))
      (Storage.withCurrent frames (TypedBorrowSteps.registeredFrame frame borrowFrame id tag)
        {TypedBorrowSteps.registeredMachine (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) tag
          with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}) := by
  exact pointer_append h prepared access projection vtable pointers choice sources budget place
    frames frame borrowFrame machine tracker enabled fresh frameBorrow id entry base tag tagEq
    ChildBorrow.fnEntryLocation ChildBorrow.fnEntryPolicy rfl frozen
    (ChildBorrow.mutable_fn_entry_initial_location true) pointer pointerWiring width cached
    globalKind globals extraWiring synchronize present addressMode inverse exposed tagMapFresh noFree fits
    .None rfl rfl rfl reference .Mut .FnEntry (by rfl) shape pointeeQuery unpin unsafeUnpin
    dereference pointeeLayout pointeeAlign placeShape sizing

end DuplicatePrefix.WildcardHitReferenceBorrow
