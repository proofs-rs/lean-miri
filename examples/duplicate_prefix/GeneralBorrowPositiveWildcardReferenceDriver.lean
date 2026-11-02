import duplicate_prefix.GeneralBorrowPositiveWildcardFnEntry
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardReferenceDriver
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
    (location : LocationTree) (head : UniIndex) (headNode : TreeNode) (extras : List UniIndex)
    (nodes : UniIndex → TreeNode) (states : UniIndex → Tree.LocationState)
    (locations : entry.allocation.extra.locations = RangeMapNonempty.homogeneous len location)
    (roots : entry.allocation.extra.roots = (head::extras).toArray)
    (headPresent : entry.allocation.extra.nodes.get head = some headNode) (headLeaf : headNode.children = #[])
    (headExposed : headNode.isExposed = true) (headStored : location.perms.get head = some unique)
    (coherent : LocationCoherent entry.allocation.extra location (registeredGlobal tracker tracker.global.nextPointerTag).protectedTags)
    (short : entry.allocation.extra.nodes.size < 65536)
    (data : ∀ root ∈ extras, entry.allocation.extra.nodes.get root = some (nodes root) ∧
      (nodes root).children = #[] ∧ (nodes root).isExposed = true ∧ location.perms.get root = some (states root) ∧
      supports (effective location (registeredGlobal tracker tracker.global.nextPointerTag).protectedTags root (nodes root)) .Read = true)
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
    (placeShape : place = RetagReferencePlace.slicePlace (Pointer.new .wildcard (Size.ofBytes base)) len place.layout) :
    let tag := tracker.global.nextPointerTag
    let tree := entry.allocation.extra
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let finalTree := GeneralBorrowPositiveWildcardConstructor.result tree
      ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩ index tag
      (.ReservedFrz false) .None ChildBorrow.fnEntryLocation 0 len
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new .wildcard (Size.ofBytes base)) len reference)
      reference.ty .FnEntry (Storage.withCurrent frames frame machine) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base (Pointer.new (.concrete id tag) (Size.ofBytes base)) len reference))
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
          {registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom) tag with
            memory := RetagEntry.updatedMemory machine.memory id entry finalTree}) := by
  let tag := tracker.global.nextPointerTag
  let tree := entry.allocation.extra
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let finalTree := GeneralBorrowPositiveWildcardConstructor.result tree
    ⟨tree.tagMapping.mapping.push (tag,index),tree.tagMapping.deassigned⟩ index tag
    (.ReservedFrz false) .None ChildBorrow.fnEntryLocation 0 len
  let before := Storage.withCurrent frames frame machine
  let after := Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
    {registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom) tag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
  let oldPointer := Pointer.new (Provenance.wildcard) (Size.ofBytes base)
  let newPointer := Pointer.new (Provenance.concrete id tag) (Size.ofBytes base)
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer len reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer len reference
  have retag := GeneralBorrowPositiveWildcardFnEntry.retag_place h prepared access projection vtable pointers choice sources budget place
    frames frame borrowFrame machine tracker enabled frameBorrow tagRoom base len id entry positive signedFits byteBounds pointer pointerWiring width
    position positionValid ordered addressRow addressMode exposedAlloc cached present race globalKind globals extraWiring synchronize frozen sizing
    location head headNode extras nodes states locations roots headPresent headLeaf headExposed headStored coherent short data tagFresh noFree fits
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
end DuplicatePrefix.GeneralBorrowPositiveWildcardReferenceDriver
