import duplicate_prefix.TypedBorrowSteps
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.TypedRetagLocal
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Input Miri.Interpreter
open TypedRetagEntry TypedRetagGeneric TypedRetagFields
theorem retag_place_local {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance) (ambient : ValidityMachine.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (capacity base offset len : UInt64)
    (rootTag : BorTag) (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (distinct : rootTag ≠ global.nextPointerTag)
    (rootUnprotected : global.protectedTags.contains rootTag = false)
    (pointer : place.mplace.ptr =
      Pointer.new (some (.concrete id rootTag)) (Size.ofBytes (base + offset)))
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K
      (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view =>
      {view with machine := {view.machine with memory}})
    (cached : ambient.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (present : ambient.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (root : entry.allocation.extra = BorrowTree.new rootTag (Size.ofBytes capacity))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (sizing : h.sizeAndAlign place (beforeTagState ambient frames frame borrowFrame global) =
      .ok (some (Size.ofBytes len, Align.ONE)) (beforeTagState ambient frames frame borrowFrame global))
    (race : ambient.machine.dataRace = none) :
    TypedRetag.retagPlace h budget place ChildBorrow.fnEntryPolicy
      (beforeTagState ambient frames frame borrowFrame global) =
      .ok (retaggedPlace place id global.nextPointerTag)
        (completedState ambient frames frame borrowFrame id entry rootTag global fresh capacity offset len) := by
  have provenance : place.mplace.ptr.provenance = some (.concrete id rootTag) := by
    rw [pointer]
    rfl
  apply TypedBorrowSteps.retag_place_at_of_reborrow h budget place ChildBorrow.fnEntryPolicy
    (Size.ofBytes len) Align.ONE (beforeTagState ambient frames frame borrowFrame global)
    (completedState ambient frames frame borrowFrame id entry rootTag global fresh capacity offset len)
    ⟨global, .FnEntry⟩ rfl fresh id (.concrete id rootTag) provenance sizing
  exact reborrow_from_fields h prepared access projection vtable pointers choice sources budget place
    ambient frames frame borrowFrame id entry capacity base offset len rootTag global fresh distinct
    rootUnprotected pointer frozen pointerWiring width globalKind globals extraWiring synchronize
    cached present root allocationSize positive signedFits bounds race

theorem retag_pointer_local {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance) (reference : LocalLayout) (ambient : ValidityMachine.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (capacity base offset len : UInt64)
    (rootTag : BorTag) (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (distinct : rootTag ≠ global.nextPointerTag)
    (rootUnprotected : global.protectedTags.contains rootTag = false)
    (pointer : place.mplace.ptr =
      Pointer.new (some (.concrete id rootTag)) (Size.ofBytes (base + offset)))
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K
      (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view =>
      {view with machine := {view.machine with memory}})
    (cached : ambient.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (present : ambient.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (root : entry.allocation.extra = BorrowTree.new rootTag (Size.ofBytes capacity))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (sizing : h.sizeAndAlign place (beforeTagState ambient frames frame borrowFrame global) =
      .ok (some (Size.ofBytes len, Align.ONE)) (beforeTagState ambient frames frame borrowFrame global))
    (placeShape : place = RetagReferencePlace.slicePlace
      (Pointer.new (.concrete id rootTag) (Size.ofBytes (base + offset))) len place.layout)
    (referenceShape : h.typeShape reference.ty = pure .reference)
    (referencePointee : h.referencePointee reference.ty = pure (place.layout.ty, .Mut))
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some place.layout.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context place.layout.ty = .ok place.layout)
    (pointeeAlign : place.layout.layout.align.abi = Align.ONE)
    (unpin : h.isUnpin place.layout.ty = pure true)
    (unsafeUnpin : h.isUnsafeUnpin place.layout.ty = pure true)
    (race : ambient.machine.dataRace = none) :
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id rootTag) (Size.ofBytes (base + offset))) len reference)
      reference.ty .FnEntry (beforeTagState ambient frames frame borrowFrame global) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) len reference))
        (completedState ambient frames frame borrowFrame id entry rootTag global fresh capacity offset len) := by
  let oldPointer := Pointer.new (Provenance.concrete id rootTag) (Size.ofBytes (base + offset))
  let newPointer := Pointer.new (Provenance.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer len reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer len reference
  have shape : h.typeShape value.layout.ty = pure .reference := referenceShape
  have pointee : h.referencePointee value.layout.ty = pure (place.layout.ty, .Mut) := referencePointee
  have policy := TypedRetagPolicyFields.new_permission h place.layout.ty (beforeTagState ambient frames frame borrowFrame global) frames
    (frameWithBorrow frame borrowFrame) rfl unpin unsafeUnpin frozen sources.implicitWrites
  have construct : h.immPtrToMPlace value = pure place := by
    rw [sources.construct]
    change PointerPlaceMachine.fromImmediate access (CompilerExecutionProviders.pointerCompiler prepared)
      choice value = pure place
    exact Eq.trans (RetagReferencePlace.canonical_from_immediate access prepared choice oldPointer len
      reference place.layout dereference pointeeLayout pointeeAlign) (congrArg pure placeShape.symm)
  have changed : retaggedPlace place id global.nextPointerTag = RetagReferencePlace.slicePlace newPointer len place.layout := by
    rw [placeShape]
    rfl
  have reconstruct : h.reconstruct value (retaggedPlace place id global.nextPointerTag) = pure output := by
    rw [sources.reconstruct, changed]
    exact RetagReferencePlace.bound_reconstruct access h value newPointer len place.layout
  exact TypedBorrowSteps.reference_pointer_of_steps h budget value output place (retaggedPlace place id global.nextPointerTag) place.layout.ty .Mut .FnEntry ChildBorrow.fnEntryPolicy
    (beforeTagState ambient frames frame borrowFrame global)
    (completedState ambient frames frame borrowFrame id entry rootTag global fresh capacity offset len)
    shape pointee policy construct
    (retag_place_local h prepared access projection vtable pointers choice sources budget place
      ambient frames frame borrowFrame id entry capacity base offset len rootTag global fresh distinct rootUnprotected pointer frozen pointerWiring width
      globalKind globals extraWiring synchronize cached present root allocationSize positive signedFits bounds sizing race)
    reconstruct

#print axioms retag_place_local
#print axioms retag_pointer_local
end DuplicatePrefix.TypedRetagLocal
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.TypedRetagLocal.retag_place_local,
      ``DuplicatePrefix.TypedRetagLocal.retag_pointer_local] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved local retag dependency {dependency}"
