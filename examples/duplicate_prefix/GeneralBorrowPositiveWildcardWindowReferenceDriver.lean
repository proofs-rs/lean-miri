import duplicate_prefix.GeneralBorrowPositiveWildcardWindowFnEntry
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowReferenceDriver
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Input Miri.Interpreter
open DuplicatePrefix.TypedBorrowSteps DuplicatePrefix.ReferenceBorrowDriver
open DuplicatePrefix.GeneralBorrowWildcardLeaf DuplicatePrefix.GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Actual positive mutable-reference FnEntry retagging from wildcard provenance.
Metadata derives policy selection, immediate-pointer decoding and reconstruction;
the physical checks, fresh tag, registration, Read and wildcard-root constructor
are derived by the typed driver from the same initial resources. -/
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
    (base offset len : UInt64) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (byteBounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (pointerFits : base.toNat+offset.toNat+len.toNat<2^64)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes (base+offset)))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (position : Nat) (positionValid : position < machine.user.addresses.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered machine.user.addresses.intToPtrMap)
    (addressRow : machine.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (beforeNext : ∀nextValid:position+1<machine.user.addresses.intToPtrMap.size,base+offset<machine.user.addresses.intToPtrMap[position+1].address)
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
    (head : UniIndex) (extras : List UniIndex)
    (leafGeometry : GeneralBorrowSparseExposedLeafState.Geometry entry.allocation.extra head extras)
    (well : entry.allocation.extra.locations.WellFormed)
    (treeBounds : offset.toNat+len.toNat≤entry.allocation.extra.locations.size.bytes.toNat)
    (sourceRaw : GeneralRangeMapState.Every (fun location=>GeneralBorrowSparseExposedLeafState.Raw entry.allocation.extra location
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags) entry.allocation.extra.locations)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag)
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
    (placeShape : place = RetagReferencePlace.slicePlace (Pointer.new .wildcard (Size.ofBytes (base+offset))) len place.layout) :
    let tag := tracker.global.nextPointerTag
    let tree := (entry.allocation.extra.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len) .Read (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree
    let index : UniIndex := ⟨UInt32.ofNat entry.allocation.extra.tagMapping.mapping.size⟩
    let finalTree := GeneralBorrowPositiveWildcardConstructor.result tree
      ⟨entry.allocation.extra.tagMapping.mapping.push (tag,index),entry.allocation.extra.tagMapping.deassigned⟩ index tag
      (.ReservedFrz false) .None ChildBorrow.fnEntryLocation offset len
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new .wildcard (Size.ofBytes (base+offset))) len reference)
      reference.ty .FnEntry (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))) len reference))
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
          {registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom) tag with
            memory := RetagEntry.updatedMemory machine.memory id entry finalTree}) := by
  let tag := tracker.global.nextPointerTag
  let tree := (entry.allocation.extra.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len) .Read (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree
  let index : UniIndex := ⟨UInt32.ofNat entry.allocation.extra.tagMapping.mapping.size⟩
  let finalTree := GeneralBorrowPositiveWildcardConstructor.result tree
    ⟨entry.allocation.extra.tagMapping.mapping.push (tag,index),entry.allocation.extra.tagMapping.deassigned⟩ index tag
    (.ReservedFrz false) .None ChildBorrow.fnEntryLocation offset len
  let before := Storage.withCurrent frames frame machine
  let after := Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
    {registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom) tag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
  let oldPointer := Pointer.new (Provenance.wildcard) (Size.ofBytes (base+offset))
  let newPointer := Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset))
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer len reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer len reference
  have retag := GeneralBorrowPositiveWildcardWindowFnEntry.retag_place h prepared access projection vtable pointers choice sources budget place
    frames frame borrowFrame machine tracker enabled frameBorrow tagRoom base offset len id entry positive signedFits byteBounds pointerFits pointer pointerWiring width
    position positionValid ordered addressRow beforeNext addressMode exposedAlloc cached present race globalKind globals extraWiring synchronize frozen sizing
    head extras leafGeometry well treeBounds sourceRaw tagFresh noFree fits
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
  exact reference_pointer_of_steps h budget value output place (TypedRetagGeneric.retaggedPlace place id tag)
    place.layout.ty .Mut .FnEntry ChildBorrow.fnEntryPolicy before after shape pointeeQuery permission construct retag reconstruct
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowReferenceDriver
