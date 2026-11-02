import duplicate_prefix.GeneralBorrowRawWildcardTypedFnEntry
import duplicate_prefix.GeneralBorrowPositiveWildcardReferenceDriver
namespace DuplicatePrefix.GeneralBorrowRawWildcardReferenceDriver
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Input Miri.Interpreter
open TypedBorrowSteps ReferenceBorrowDriver
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Actual wildcard mutable reference decoding, permission selection, retagging
and reconstruction retain the derived raw Both Positive on its exact tree. -/
theorem pointer {K U C F A : Type} [DecidableEq K]
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
    (enabled : machine.borrowTracker = some tracker) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (tagRoom : tracker.global.nextPointerTag.value < 18446744073709551615)
    (base len : UInt64) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (byteBounds : len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes base))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (position : Nat) (positionValid : position < machine.user.addresses.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered machine.user.addresses.intToPtrMap)
    (addressRow : machine.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (exposedAlloc : machine.user.addresses.exposed.contains id = true)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (sizing : h.sizeAndAlign place (Storage.withCurrent frames frame machine) =
      .ok (some (Size.ofBytes len,Align.ONE)) (Storage.withCurrent frames frame machine))
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (capability : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags none none none 0 len)
    (distinct : entry.allocation.extra.roots.toList.Nodup)
    (short : entry.allocation.extra.nodes.size < 65536)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295)
    (reference : LocalLayout)
    (shape : h.typeShape reference.ty = pure .reference)
    (pointeeQuery : h.referencePointee reference.ty = pure (place.layout.ty,.Mut))
    (unpin : h.isUnpin place.layout.ty = pure true)
    (unsafeUnpin : h.isUnsafeUnpin place.layout.ty = pure true)
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some place.layout.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context place.layout.ty = .ok place.layout)
    (pointeeAlign : place.layout.layout.align.abi = Align.ONE)
    (placeShape : place = RetagReferencePlace.slicePlace (Pointer.new .wildcard (Size.ofBytes base)) len place.layout) :
    ∃ output : GeneralBorrowForestFnEntry.Output,
      GeneralBorrowRawWildcardFnEntryRuntime.operation entry.allocation.extra tracker.global borrowFrame id 0 len = .ok output ∧
      TypedRetag.retagPtrValue h budget
        (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new .wildcard (Size.ofBytes base)) len reference)
        reference.ty .FnEntry (Storage.withCurrent frames frame machine) =
        .ok (some (RetagReferencePlace.sliceValue access.runtime.base
          (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes base)) len reference))
          (Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
            {registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom) tracker.global.nextPointerTag with
              memory := RetagEntry.updatedMemory machine.memory id entry output.child.tree}) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      ∃ child,output.child.tree.indexOfTag tracker.global.nextPointerTag = some child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive output.child.tree output.global.protectedTags
          (some child) (some child) (some tracker.global.nextPointerTag) 0 len) := by
  obtain ⟨result,run,retag,afterRuntime,child,lookup,both⟩ := GeneralBorrowRawWildcardTypedFnEntry.retag_place h prepared access projection vtable pointers choice sources budget place
    frames frame borrowFrame machine tracker enabled frameBorrow tagRoom base len id entry positive signedFits byteBounds pointer pointerWiring width
    position positionValid ordered addressRow addressMode exposedAlloc cached present race globalKind globals extraWiring synchronize frozen sizing
    runtime capability distinct short nodeRoom
  let tag := tracker.global.nextPointerTag
  let finalTree := result.child.tree
  let before := Storage.withCurrent frames frame machine
  let after := Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
    {registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom) tag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
  let oldPointer := Pointer.new (Provenance.wildcard) (Size.ofBytes base)
  let newPointer := Pointer.new (Provenance.concrete id tag) (Size.ofBytes base)
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer len reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer len reference
  have permission := TypedRetagPolicyFields.new_permission_general h place.layout.ty .Mutable .FnEntry before frames frame rfl
    unpin unsafeUnpin frozen sources.implicitWrites
  have created : RetagPolicy.create ⟨true,true,true⟩ .Mutable .FnEntry ⟨false,false⟩ = some ChildBorrow.fnEntryPolicy := rfl
  rw [created] at permission
  have construct : h.immPtrToMPlace value = pure place := by
    rw [sources.construct]
    exact Eq.trans (RetagReferencePlace.canonical_from_immediate access prepared choice oldPointer len reference
      place.layout dereference pointeeLayout pointeeAlign) (congrArg pure placeShape.symm)
  have changed : TypedRetagGeneric.retaggedPlace place id tag = RetagReferencePlace.slicePlace newPointer len place.layout := by
    rw [placeShape];rfl
  have reconstruct : h.reconstruct value (TypedRetagGeneric.retaggedPlace place id tag) = pure output := by
    rw [sources.reconstruct,changed]
    exact RetagReferencePlace.bound_reconstruct access h value newPointer len place.layout
  have pointerResult := reference_pointer_of_steps h budget value output place (TypedRetagGeneric.retaggedPlace place id tag)
    place.layout.ty .Mut .FnEntry ChildBorrow.fnEntryPolicy before after shape pointeeQuery permission construct retag reconstruct
  exact ⟨result,run,pointerResult,afterRuntime,child,lookup,both⟩
end DuplicatePrefix.GeneralBorrowRawWildcardReferenceDriver
