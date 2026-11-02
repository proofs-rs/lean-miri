import duplicate_prefix.ConcreteEmptyPoolEntry
import duplicate_prefix.ConcreteEmptyReferenceBorrow

namespace DuplicatePrefix.ConcretePoolReferenceBorrow
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Input Miri.Interpreter
open TypedBorrowSteps ReferenceBorrowDriver
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
attribute [local irreducible] UniValMap.insert

/-- Actual concrete empty FnEntry from a mapped parent in an arbitrary ranked
forest and either actual allocator branch. Zero length requires no positive
permission window or artificial offset bounds. The child equation is DERIVED. -/
theorem fnentry_pointer {K U C F A : Type} [DecidableEq K]
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
    (base offset : UInt64) (parentTag tag : BorTag)
    (tagEq : tag = tracker.global.nextPointerTag)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes (base+offset)))
    (_pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (entryInput : ConcreteEmptyPoolEntry.Input entry.allocation.extra parentTag tag)
    (reference : LocalLayout)
    (shape : h.typeShape reference.ty = pure .reference)
    (pointeeQuery : h.referencePointee reference.ty = pure (place.layout.ty,.Mut))
    (unpin : h.isUnpin place.layout.ty = pure true)
    (unsafeUnpin : h.isUnsafeUnpin place.layout.ty = pure true)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some place.layout.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context place.layout.ty = .ok place.layout)
    (pointeeAlign : place.layout.layout.align.abi = Align.ONE)
    (placeShape : place = RetagReferencePlace.slicePlace
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 place.layout)
    (sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes 0,Align.ONE)) (Storage.withCurrent frames frame machine)) :
    let finalTree := entryInput.after
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference)
      reference.ty .FnEntry (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))) 0 reference))
      (Storage.withCurrent frames (TypedBorrowSteps.registeredFrame frame borrowFrame id tag)
        {TypedBorrowSteps.registeredMachine (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) tag
          with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}) := by
  exact ConcreteEmptyReferenceBorrow.live_zero_reference_pointer h prepared access projection vtable pointers choice sources budget place
    frames frame borrowFrame machine tracker enabled fresh frameBorrow id entry base offset parentTag tag tagEq
    ChildBorrow.fnEntryLocation ChildBorrow.fnEntryPolicy rfl frozen
    (ChildBorrow.mutable_fn_entry_initial_location true) pointer _pointerWiring width cached
    globalKind globals extraWiring synchronize present entryInput.after
    (by simpa only [ChildBorrow.fnEntryLocation,ChildBorrow.fnEntryPolicy,GeneralBorrowFreshChild.inside,Size.ZERO,Size.ofBytes,Option.isSome_some] using entryInput.child offset)
    reference .Mut .FnEntry (by rfl) shape pointeeQuery unpin unsafeUnpin dereference pointeeLayout pointeeAlign placeShape sizing

end DuplicatePrefix.ConcretePoolReferenceBorrow
