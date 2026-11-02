import duplicate_prefix.TypedBorrowSteps
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.ReferenceBorrowDriver
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Input Miri.Interpreter
open TypedBorrowSteps

def allocatedTracker (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) : MachineHooks.BorrowState :=
  {tracker with global := {tracker.global with nextPointerTag := TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh}}
def allocatedMachine {K U : Type} (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) : MachineHooks.MachineState K U :=
  {machine with borrowTracker := some (allocatedTracker tracker fresh)}

theorem protected_reference_pointer {K U C F A : Type} [DecidableEq K]
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
    (base offset len : UInt64) (parentTag : BorTag) (tag : BorTag)
    (tagEq : tag = tracker.global.nextPointerTag)
    (initial : Tree.LocationState) (policy : RetagPolicy.NewPermission)
    (protection : policy.protector = some .StrongProtector)
    (associated : initial.permission.associatedAccess = some .Read)
    (positive : (0 : UInt64) < len)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (initialState : RetagPolicy.initialLocationState policy true = .ok initial)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes (base + offset)))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none) (parentTree finalTree : BorrowTree)
    (readTree : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read (registeredGlobal tracker tag).protectedTags .VisitChildrenOfAccessed).tree = parentTree)
    (readDone : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read (registeredGlobal tracker tag).protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (child : parentTree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes len) initial) policy.outsidePermission policy.protector.isSome =
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
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len place.layout)
    (sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes len,Align.ONE)) (Storage.withCurrent frames frame machine)) :
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len reference)
      reference.ty mode (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))) len reference))
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
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer len reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer len reference
  have reborrow := TypedBorrowSteps.protected_read_from_fields h prepared access projection vtable pointers choice sources
    budget place frames frame borrowFrame (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh)
    rfl frameBorrow id entry base offset len parentTag tracker.global.nextPointerTag initial policy protection associated
    positive frozen initialState pointer pointerWiring width cached signedFits bounds globalKind globals extraWiring synchronize
    present race parentTree finalTree readTree readDone child
  have retag := TypedBorrowSteps.retag_place_at_of_reborrow h budget place policy (Size.ofBytes len) Align.ONE
    before after tracker enabled fresh id (.concrete id parentTag) (by rw [pointer]; rfl) sizing reborrow
  have permission := TypedRetagPolicyFields.new_permission_general h place.layout.ty
    (if mutability == .Mut then .Mutable else .Shared) mode before frames frame rfl
    unpin unsafeUnpin frozen sources.implicitWrites
  rw [created] at permission
  have construct : h.immPtrToMPlace value = pure place := by
    rw [sources.construct]
    exact Eq.trans (RetagReferencePlace.canonical_from_immediate access prepared choice oldPointer len reference
      place.layout dereference pointeeLayout pointeeAlign) (congrArg pure placeShape.symm)
  have changed : TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag =
      RetagReferencePlace.slicePlace newPointer len place.layout := by rw [placeShape]; rfl
  have reconstruct : h.reconstruct value (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) = pure output := by
    rw [sources.reconstruct, changed]
    exact RetagReferencePlace.bound_reconstruct access h value newPointer len place.layout
  exact TypedBorrowSteps.reference_pointer_of_steps h budget value output place
    (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) place.layout.ty mutability mode policy
    before after shape pointeeQuery permission construct retag reconstruct

theorem unprotected_reference_pointer {K U C F A : Type} [DecidableEq K]
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
    (base offset len : UInt64) (parentTag : BorTag) (tag : BorTag)
    (tagEq : tag = tracker.global.nextPointerTag)
    (initial : Tree.LocationState) (policy : RetagPolicy.NewPermission)
    (protection : policy.protector = none)
    (associated : initial.permission.associatedAccess = some .Read)
    (positive : (0 : UInt64) < len)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (initialState : RetagPolicy.initialLocationState policy true = .ok initial)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes (base + offset)))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none) (parentTree finalTree : BorrowTree)
    (readTree : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree = parentTree)
    (readDone : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (child : parentTree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes len) initial) policy.outsidePermission policy.protector.isSome =
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
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len place.layout)
    (sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes len,Align.ONE)) (Storage.withCurrent frames frame machine)) :
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len reference)
      reference.ty mode (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))) len reference))
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
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer len reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer len reference
  have reborrow := TypedBorrowSteps.unprotected_read_from_fields h prepared access projection vtable pointers choice sources
    budget place frames frame (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh)
    rfl id entry base offset len parentTag tracker.global.nextPointerTag initial policy protection associated
    positive frozen initialState pointer pointerWiring width cached signedFits bounds globalKind globals extraWiring synchronize
    present race parentTree finalTree readTree readDone child
  have retag := TypedBorrowSteps.retag_place_at_of_reborrow h budget place policy (Size.ofBytes len) Align.ONE
    before after tracker enabled fresh id (.concrete id parentTag) (by rw [pointer]; rfl) sizing reborrow
  have permission := TypedRetagPolicyFields.new_permission_general h place.layout.ty
    (if mutability == .Mut then .Mutable else .Shared) mode before frames frame rfl
    unpin unsafeUnpin frozen sources.implicitWrites
  rw [created] at permission
  have construct : h.immPtrToMPlace value = pure place := by
    rw [sources.construct]
    exact Eq.trans (RetagReferencePlace.canonical_from_immediate access prepared choice oldPointer len reference
      place.layout dereference pointeeLayout pointeeAlign) (congrArg pure placeShape.symm)
  have changed : TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag =
      RetagReferencePlace.slicePlace newPointer len place.layout := by rw [placeShape]; rfl
  have reconstruct : h.reconstruct value (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) = pure output := by
    rw [sources.reconstruct, changed]
    exact RetagReferencePlace.bound_reconstruct access h value newPointer len place.layout
  exact TypedBorrowSteps.reference_pointer_of_steps h budget value output place
    (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) place.layout.ty mutability mode policy
    before after shape pointeeQuery permission construct retag reconstruct

#print axioms protected_reference_pointer

end DuplicatePrefix.ReferenceBorrowDriver
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ReferenceBorrowDriver.protected_reference_pointer,
      ``DuplicatePrefix.ReferenceBorrowDriver.unprotected_reference_pointer] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved reference borrow driver dependency {dependency}"
