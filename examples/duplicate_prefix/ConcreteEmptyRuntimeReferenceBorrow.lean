import duplicate_prefix.ConcreteEmptyReferenceBorrow
import duplicate_prefix.ConcreteEmptyRuntimeEntry

namespace DuplicatePrefix.ConcreteEmptyRuntimeReferenceBorrow
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Input Miri.Interpreter
open TypedBorrowSteps ReferenceBorrowDriver
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Real protected zero-sized Default reference retagging on an arbitrary
formed forest with any coherent free pool. The constructor success assumed by
the lower-level driver is derived from raw graph/allocator/SIFA/Clean and
counter high-water data. No BorrowTree.new, noFree, byte ownership, source
initialization, offset bounds or successful-operation premise is required.
Compiler/policy/ABI dictionary equalities and raw slice-layout/metadata facts
remain explicit; even the zero dynamic-size result is derived from those facts.
This is a typed retag operation, not an all-count function theorem. -/
theorem live_zero_reference_pointer {K U C F A : Type} [DecidableEq K]
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
    (formed : GeneralBorrowStructuralHistorySifaState.Formed entry.allocation.extra tracker.global.protectedTags)
    (below : GeneralBorrowForestTagHighWater.Below entry.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (parent : UniIndex) (parentNode : TreeNode)
    (parentTagged : entry.allocation.extra.indexOfTag parentTag = some parent)
    (parentPresent : entry.allocation.extra.nodeAt parent = some parentNode)
    (room : entry.allocation.extra.nodes.size + 1 ≤ 4294967295)
    (initialDefault : initial = GeneralBorrowFreshChild.inside)
    (outsideDefault : policy.outsidePermission = .ReservedFrz false)
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
    (slice : TypedRetagEntry.SliceFacts projection choice place 0) :
    let input := ConcreteEmptyRuntimeEntry.form entry.allocation.extra tracker.global.protectedTags parentTag tag
      formed parent parentNode parentTagged parentPresent
      (by rw [tagEq]; exact ConcreteEmptyRuntimeEntry.counter_fresh entry.allocation.extra tracker.global below) room
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference)
      reference.ty mode (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))) 0 reference))
      (Storage.withCurrent frames (TypedBorrowSteps.registeredFrame frame borrowFrame id tag)
        {TypedBorrowSteps.registeredMachine (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) tag
          with memory := RetagEntry.updatedMemory machine.memory id entry input.after}) := by
  let input := ConcreteEmptyRuntimeEntry.form entry.allocation.extra tracker.global.protectedTags parentTag tag
      formed parent parentNode parentTagged parentPresent
      (by rw [tagEq]; exact ConcreteEmptyRuntimeEntry.counter_fresh entry.allocation.extra tracker.global below) room
  have child : entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes 0) initial) policy.outsidePermission policy.protector.isSome =
      ⟨input.after, .ok ()⟩ := by
    rw [initialDefault, outsideDefault, protection]
    exact input.child offset
  have sizeFields := TypedRetagFields.size_from_fields h prepared access projection vtable pointers choice sources place 0 slice
  have sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes 0, Align.ONE)) (Storage.withCurrent frames frame machine) := by
    rw [sizeFields]
    rfl
  exact ConcreteEmptyReferenceBorrow.live_zero_reference_pointer
      h prepared access projection vtable pointers choice sources
      budget place frames frame borrowFrame machine tracker enabled
      fresh frameBorrow id entry base offset parentTag tag
      tagEq initial policy protection frozen initialState pointer pointerWiring
      width cached globalKind globals extraWiring synchronize present input.after
      child reference mutability mode created shape pointeeQuery unpin
      unsafeUnpin dereference pointeeLayout pointeeAlign placeShape sizing

end
end DuplicatePrefix.ConcreteEmptyRuntimeReferenceBorrow
