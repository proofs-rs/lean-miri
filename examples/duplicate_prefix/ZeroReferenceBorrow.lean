import duplicate_prefix.ReferenceBorrowDriver
import duplicate_prefix.RootEmptyReferenceValidity
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.ZeroReferenceBorrow
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Input Miri.Interpreter
open ReferenceBorrowDriver
theorem unprotected_live_zero_pointer {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (base offset : UInt64) (parentTag : BorTag) (tag : BorTag)
    (tagEq : tag = tracker.global.nextPointerTag)
    (initial : Tree.LocationState) (policy : RetagPolicy.NewPermission)
    (protection : policy.protector = none)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (initialState : RetagPolicy.initialLocationState policy true = .ok initial)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes (base + offset)))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (finalTree : BorrowTree)
    (child : entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new Size.ZERO initial) policy.outsidePermission policy.protector.isSome =
      ⟨finalTree, .ok ()⟩)
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
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 place.layout)
    (sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes 0,Align.ONE)) (Storage.withCurrent frames frame machine)) :
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference)
      reference.ty mode (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))) 0 reference))
      (Storage.withCurrent frames frame
        {allocatedMachine machine tracker fresh
          with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}) := by
  subst tag
  let before := Storage.withCurrent frames frame machine
  let after := Storage.withCurrent frames frame
    {allocatedMachine machine tracker fresh
      with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
  let oldPointer := Pointer.new (Provenance.concrete id parentTag) (Size.ofBytes (base+offset))
  let newPointer := Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer 0 reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer 0 reference
  let allocated := Storage.withCurrent frames frame (allocatedMachine machine tracker fresh)
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO allocated = .ok () allocated := by
    rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access place.mplace.ptr allocated
  have resolve : h.resolveAllocation place.mplace.ptr allocated =
      .ok (some ⟨id,Size.ofBytes offset,.concrete parentTag⟩) allocated := by
    rw [sources.resolve, pointer]
    exact RetagPointerChecks.resolve_allocation_cached pointers allocated id parentTag base offset width cached
  have inside := TypedRetagPolicyFields.inside_for_policy h budget place Size.ZERO policy initial initialState
    sources.precise frozen
  have reborrow := TypedBorrowSteps.unprotected_live_zero_of_steps h budget place frames frame
    (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) rfl id entry offset
    (.concrete parentTag) tracker.global.nextPointerTag initial policy protection check resolve
    (by rw [sources.log]) inside globalKind globals (Eq.trans sources.ensure extraWiring) synchronize present finalTree child
  have retag := TypedBorrowSteps.retag_place_at_of_reborrow h budget place policy Size.ZERO Align.ONE
    before after tracker enabled fresh id (.concrete id parentTag) (by rw [pointer]; rfl) sizing reborrow
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

theorem protected_live_zero_pointer {K U C F A : Type} [DecidableEq K]
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
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (base offset : UInt64) (parentTag : BorTag) (tag : BorTag)
    (tagEq : tag = tracker.global.nextPointerTag)
    (initial : Tree.LocationState) (policy : RetagPolicy.NewPermission)
    (protection : policy.protector = some .StrongProtector)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (initialState : RetagPolicy.initialLocationState policy true = .ok initial)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes (base + offset)))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (finalTree : BorrowTree)
    (child : entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new Size.ZERO initial) policy.outsidePermission policy.protector.isSome =
      ⟨finalTree, .ok ()⟩)
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
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 place.layout)
    (sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes 0,Align.ONE)) (Storage.withCurrent frames frame machine)) :
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference)
      reference.ty mode (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))) 0 reference))
      (Storage.withCurrent frames (TypedBorrowSteps.registeredFrame frame borrowFrame id tag)
        {TypedBorrowSteps.registeredMachine (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) tag
          with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}) := by
  subst tag
  let before := Storage.withCurrent frames frame machine
  let after := Storage.withCurrent frames (TypedBorrowSteps.registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
    {TypedBorrowSteps.registeredMachine (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) tracker.global.nextPointerTag
      with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
  let oldPointer := Pointer.new (Provenance.concrete id parentTag) (Size.ofBytes (base+offset))
  let newPointer := Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer 0 reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer 0 reference
  let allocated := Storage.withCurrent frames frame (allocatedMachine machine tracker fresh)
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO allocated = .ok () allocated := by
    rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access place.mplace.ptr allocated
  have resolve : h.resolveAllocation place.mplace.ptr allocated =
      .ok (some ⟨id,Size.ofBytes offset,.concrete parentTag⟩) allocated := by
    rw [sources.resolve, pointer]
    exact RetagPointerChecks.resolve_allocation_cached pointers allocated id parentTag base offset width cached
  have inside := TypedRetagPolicyFields.inside_for_policy h budget place Size.ZERO policy initial initialState
    sources.precise frozen
  have reborrow := TypedBorrowSteps.protected_live_zero_of_steps h budget place frames frame borrowFrame
    (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) rfl frameBorrow id entry offset
    (.concrete parentTag) tracker.global.nextPointerTag initial policy protection check resolve
    (by rw [sources.log]) inside globalKind globals (Eq.trans sources.ensure extraWiring) synchronize present finalTree child
  have retag := TypedBorrowSteps.retag_place_at_of_reborrow h budget place policy Size.ZERO Align.ONE
    before after tracker enabled fresh id (.concrete id parentTag) (by rw [pointer]; rfl) sizing reborrow
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

theorem no_provenance_zero_pointer {K U C F A : Type} [DecidableEq K]
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
    (sizingAt : h.sizeAndAlign (RetagReferencePlace.integerSlicePlace address 0 pointee) state =
      .ok (some (Size.ZERO, Align.ONE)) state) :
    TypedRetag.machineRetagPtrValue h budget (RetagReferencePlace.integerSliceValue address 0 reference)
      reference.ty state = .ok (some (RetagReferencePlace.integerSliceValue address 0 reference))
        (TypedRetagEmpty.afterTag state tracker fresh) := by
  let value := RetagReferencePlace.integerSliceValue address 0 reference
  let place := RetagReferencePlace.integerSlicePlace address 0 pointee
  have construct : h.immPtrToMPlace value = pure place := by
    rw [sources.construct]
    exact RetagReferencePlace.canonical_from_integer access prepared choice address 0 reference pointee
      dereference pointeeLayout pointeeAlign width
  have reborrow := TypedBorrowSteps.no_provenance_zero_from_fields h prepared access projection vtable
    pointers choice sources budget place policy tracker.global.nextPointerTag
    (TypedRetagEmpty.afterTag state tracker fresh) rfl
  have retag := RootEmptyReferenceValidity.no_provenance_zero_retag_place_at h budget place policy
    Align.ONE state tracker enabled fresh rfl sizingAt reborrow
  have permission := TypedRetagPolicyFields.new_permission_general h pointee.ty
    (if mutability == .Mut then .Mutable else .Shared) retagMode state frames frame frameShape
    unpin unsafeUnpin frozen sources.implicitWrites
  rw [created] at permission
  have reconstruct : h.reconstruct value place = pure value := by
    rw [sources.reconstruct]
    funext after
    simp [TypedMachineBindings.retagHooks, value, place, RetagReferencePlace.integerSlicePlace,
      RetagReferencePlace.integerSliceValue, MemPlace.toRef, Immediate.newPointerWithMeta,
      RetagReferencePlace.integer_from_pointer access.runtime.base address width,
      Except.mapError, Except.bind, Except.pure, bind, EStateM.bind, pure, EStateM.pure]
  have result := TypedBorrowSteps.reference_pointer_of_steps h budget value value place place pointee.ty mutability
    retagMode policy state (TypedRetagEmpty.afterTag state tracker fresh)
    shape pointeeQuery permission construct retag reconstruct
  unfold TypedRetag.machineRetagPtrValue
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, enabled, modeEq]
  exact result

theorem unprotected_nonlive_zero_pointer {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (info : AllocationInfo)
    (metadata : machine.memory.getAllocInfo id = .ok info) (nonlive : info.kind ≠ .liveData)
    (base offset : UInt64) (parentTag : BorTag) (tag : BorTag)
    (tagEq : tag = tracker.global.nextPointerTag)
    (policy : RetagPolicy.NewPermission)
    (protection : policy.protector = none)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes (base + offset)))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
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
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 place.layout)
    (sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes 0,Align.ONE)) (Storage.withCurrent frames frame machine)) :
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference)
      reference.ty mode (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))) 0 reference))
      (Storage.withCurrent frames frame (allocatedMachine machine tracker fresh)) := by
  subst tag
  let before := Storage.withCurrent frames frame machine
  let after := Storage.withCurrent frames frame (allocatedMachine machine tracker fresh)
  let oldPointer := Pointer.new (Provenance.concrete id parentTag) (Size.ofBytes (base+offset))
  let newPointer := Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer 0 reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer 0 reference
  let allocated := Storage.withCurrent frames frame (allocatedMachine machine tracker fresh)
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO allocated = .ok () allocated := by
    rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access place.mplace.ptr allocated
  have resolve : h.resolveAllocation place.mplace.ptr allocated =
      .ok (some ⟨id,Size.ofBytes offset,.concrete parentTag⟩) allocated := by
    rw [sources.resolve, pointer]
    exact RetagPointerChecks.resolve_allocation_cached pointers allocated id parentTag base offset width cached
  have reborrow : TypedRetag.reborrow h budget place Size.ZERO policy tracker.global.nextPointerTag allocated =
      .ok (some (.concrete id tracker.global.nextPointerTag)) allocated := by
    unfold TypedRetag.reborrow
    simp only [check, resolve, sources.log, bind, EStateM.bind, pure, EStateM.pure]
    rw [protection]
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
    unfold_typed ".TypedRetag.checked"
    simp only [allocated, Storage.withCurrent, ReferenceBorrowDriver.allocatedMachine, metadata,
      bind, EStateM.bind, pure, EStateM.pure]
    simp [nonlive, Size.ZERO, allocated, bind, EStateM.bind, pure, EStateM.pure]
  have retag := TypedBorrowSteps.retag_place_at_of_reborrow h budget place policy Size.ZERO Align.ONE
    before after tracker enabled fresh id (.concrete id parentTag) (by rw [pointer]; rfl) sizing reborrow
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

theorem protected_nonlive_zero_pointer {K U C F A : Type} [DecidableEq K]
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
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (info : AllocationInfo)
    (metadata : machine.memory.getAllocInfo id = .ok info) (nonlive : info.kind ≠ .liveData)
    (base offset : UInt64) (parentTag : BorTag) (tag : BorTag)
    (tagEq : tag = tracker.global.nextPointerTag)
    (policy : RetagPolicy.NewPermission)
    (protection : policy.protector = some .StrongProtector)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes (base + offset)))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
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
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 place.layout)
    (sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes 0,Align.ONE)) (Storage.withCurrent frames frame machine)) :
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference)
      reference.ty mode (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))) 0 reference))
      (TypedBorrowSteps.registeredState frames frame borrowFrame (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) id tag) := by
  subst tag
  let before := Storage.withCurrent frames frame machine
  let after := TypedBorrowSteps.registeredState frames frame borrowFrame (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) id tracker.global.nextPointerTag
  let oldPointer := Pointer.new (Provenance.concrete id parentTag) (Size.ofBytes (base+offset))
  let newPointer := Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer 0 reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer 0 reference
  let allocated := Storage.withCurrent frames frame (allocatedMachine machine tracker fresh)
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO allocated = .ok () allocated := by
    rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access place.mplace.ptr allocated
  have resolve : h.resolveAllocation place.mplace.ptr allocated =
      .ok (some ⟨id,Size.ofBytes offset,.concrete parentTag⟩) allocated := by
    rw [sources.resolve, pointer]
    exact RetagPointerChecks.resolve_allocation_cached pointers allocated id parentTag base offset width cached
  have reborrow := TypedBorrowSteps.protected_nonlive_zero_of_metadata h budget place frames frame borrowFrame
    (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) rfl frameBorrow id offset (.concrete parentTag)
    tracker.global.nextPointerTag policy protection info metadata nonlive check resolve (by rw [sources.log])
  have retag := TypedBorrowSteps.retag_place_at_of_reborrow h budget place policy Size.ZERO Align.ONE
    before after tracker enabled fresh id (.concrete id parentTag) (by rw [pointer]; rfl) sizing reborrow
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

#print axioms unprotected_live_zero_pointer
end DuplicatePrefix.ZeroReferenceBorrow
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ZeroReferenceBorrow.unprotected_live_zero_pointer,
      ``DuplicatePrefix.ZeroReferenceBorrow.protected_live_zero_pointer,
      ``DuplicatePrefix.ZeroReferenceBorrow.no_provenance_zero_pointer,
      ``DuplicatePrefix.ZeroReferenceBorrow.unprotected_nonlive_zero_pointer,
      ``DuplicatePrefix.ZeroReferenceBorrow.protected_nonlive_zero_pointer] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved zero reference driver dependency {dependency}"
