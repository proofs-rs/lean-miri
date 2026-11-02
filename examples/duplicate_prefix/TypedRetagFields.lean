import duplicate_prefix.TypedRetagGeneric
import duplicate_prefix.TypedRetagPolicyFields

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.TypedRetagFields
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Input Miri.Interpreter
open TypedRetagEntry
open TypedRetagGeneric
open Lean Elab

private def proofName (suffix : String) : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected exact checked source composition theorem {suffix}"
elab "core_reborrow_stage" : term => return mkConst (← proofName ".TypedRetagGeneric.reborrow_stage")
elab "core_place_stage" : term => return mkConst (← proofName ".TypedRetagGeneric.retag_place_stage")
elab "core_pointer_stage" : term => return mkConst (← proofName ".TypedRetagGeneric.retag_pointer_stage")

/-- Dictionary identities of the canonical source implementations, plus the
fixed retag configuration; these assert no runtime operation succeeds. -/
structure SourceFields {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C) where
  check : h.checkPtrAccess = ValidityMachine.checkPointerAccess access
  resolve : h.resolveAllocation = TypedValidityProviders.resolveAllocation pointers
  ensure : h.ensureTreeExtra = pointers.ensureTreeExtra
  log : h.logCreation = fun _ _ _ _ _ => pure ()
  precise : h.preciseInteriorMut = pure false
  implicitWrites : h.implicitWrites = pure false
  construct : h.immPtrToMPlace =
    PointerPlaceMachine.fromImmediate access (CompilerExecutionProviders.pointerCompiler prepared) choice
  sizing : h.sizeAndAlign = fun place =>
    DynamicLayout.sizeAndAlignFromMeta (PlaceDynamic.withVTable projection.dynamic vtable)
      choice projection.dynamicFuel place.mplace.metadata place.layout
  reconstruct : h.reconstruct = (TypedMachineBindings.retagHooks access h).reconstruct

theorem eval_sources {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (compiler : CompilerProviders.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C) :
    SourceFields (EvalRetagMachine.hooks prepared runtime
      (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice)
      prepared access projection vtable pointers choice := by
  constructor <;> rfl

theorem adapted_sources {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (base : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (log : base.logCreation = fun _ _ _ _ _ => pure ())
    (precise : base.preciseInteriorMut = pure false)
    (implicitWrites : base.implicitWrites = pure false) :
    SourceFields (TypedValidityProviders.retagHooks prepared runtime access projection vtable pointers choice base)
      prepared access projection vtable pointers choice := by
  constructor
  · rfl
  · rfl
  · rfl
  · exact log
  · exact precise
  · exact implicitWrites
  · rfl
  · rfl
  · rfl

structure ReferenceQueries {K U : Type} (h : TypedRetag.Hooks K U) (reference pointee : TyId) where
  shape : h.typeShape reference = pure .reference
  pointee_eq : h.referencePointee reference = pure (pointee, .Mut)
  unpin : h.isUnpin pointee = pure true
  unsafeUnpin : h.isUnsafeUnpin pointee = pure true
  freeze : h.typeIsFreeze pointee = pure true

theorem adapted_reference_queries {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (base : TypedRetag.Hooks K (ValidityMachine.UserState U)) (reference pointee : TyId)
    (shape : CompilerFacts.retagTypeShape prepared.context reference = .ok .reference)
    (pointeeQuery : CompilerFacts.referencePointee prepared.context reference = .ok (pointee, .Mut))
    (unpin : CompilerFacts.boolean prepared.context pointee "is_unpin" = .ok true)
    (unsafeUnpin : CompilerFacts.boolean prepared.context pointee "is_unsafe_unpin" = .ok true)
    (freeze : CompilerFacts.boolean prepared.context pointee "is_freeze" = .ok true) :
    ReferenceQueries
      (TypedValidityProviders.retagHooks prepared runtime access projection vtable pointers choice base)
      reference pointee := by
  constructor
  all_goals
    simp only [TypedValidityProviders.retagHooks, CompilerFacts.typedRetagHooks, TypedMachineBindings.retagHooks]
    unfold_typed ".CompilerFacts.lift"
    simp only [shape, pointeeQuery, unpin, unsafeUnpin, freeze]

theorem size_from_fields {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : SourceFields h prepared access projection vtable pointers choice)
    (place : MPlaceTy Provenance) (len : UInt64) (facts : SliceFacts projection choice place len) :
    h.sizeAndAlign place = pure (some (Size.ofBytes len, Align.ONE)) := by
  rw [sources.sizing]
  dsimp only
  rw [facts.fuel_eq, facts.metadata_eq]
  exact SliceDynamicLayout.u8_slice_size _ choice facts.fuel place.layout facts.element len
    facts.unsized facts.kind facts.field facts.elementSize facts.elementAlign facts.width facts.bounded

theorem reborrow_from_fields {K U C F A : Type} [DecidableEq K]
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
    (race : ambient.machine.dataRace = none) :
    TypedRetag.reborrow h budget place (Size.ofBytes len) ChildBorrow.fnEntryPolicy
      global.nextPointerTag (entryState ambient frames frame borrowFrame global fresh) =
      .ok (some (.concrete id global.nextPointerTag))
        {protectedState ambient frames frame borrowFrame id global fresh with machine :=
          {(protectedState ambient frames frame borrowFrame id global fresh).machine with
            memory := RetagEntry.updatedMemory ambient.machine.memory id entry
              (childTree rootTag global.nextPointerTag capacity offset len)}} := by
  have checked : h.checkPtrAccess place.mplace.ptr (Size.ofBytes len)
      (entryState ambient frames frame borrowFrame global fresh) =
      .ok () (entryState ambient frames frame borrowFrame global fresh) := by
    rw [sources.check]
    rw [pointer]
    exact RetagPointerChecks.check_pointer_access_cached pointers access
      (entryState ambient frames frame borrowFrame global fresh) id rootTag base offset len entry
      pointerWiring width cached present positive signedFits (by simpa only [allocationSize, Size.ofBytes] using bounds)
  have resolved : h.resolveAllocation place.mplace.ptr
      (entryState ambient frames frame borrowFrame global fresh) =
      .ok (some ⟨id, Size.ofBytes offset, .concrete rootTag⟩)
        (entryState ambient frames frame borrowFrame global fresh) := by
    rw [sources.resolve]
    rw [pointer]
    exact RetagPointerChecks.resolve_allocation_cached pointers
      (entryState ambient frames frame borrowFrame global fresh) id rootTag base offset width cached
  exact core_reborrow_stage h budget place ambient frames frame borrowFrame id entry capacity offset len
    rootTag global fresh distinct rootUnprotected checked resolved (by rw [sources.log])
    (TypedRetagPolicyFields.inside_permissions h budget place (Size.ofBytes len) sources.precise frozen)
    globalKind globals (Eq.trans sources.ensure extraWiring) synchronize present root positive bounds race

theorem retag_place_from_fields {K U C F A : Type} [DecidableEq K]
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
    (slice : SliceFacts projection choice place len)
    (race : ambient.machine.dataRace = none) :
    TypedRetag.retagPlace h budget place ChildBorrow.fnEntryPolicy
      (beforeTagState ambient frames frame borrowFrame global) =
      .ok (retaggedPlace place id global.nextPointerTag)
        (completedState ambient frames frame borrowFrame id entry rootTag global fresh capacity offset len) := by
  have provenance : place.mplace.ptr.provenance = some (.concrete id rootTag) := by
    rw [pointer]
    rfl
  exact core_place_stage h budget place ambient frames frame borrowFrame id entry capacity offset len rootTag global fresh
    (size_from_fields h prepared access projection vtable pointers choice sources place len slice)
    provenance
    (reborrow_from_fields h prepared access projection vtable pointers choice sources budget place
      ambient frames frame borrowFrame id entry capacity base offset len rootTag global fresh distinct rootUnprotected pointer frozen pointerWiring width
      globalKind globals extraWiring synchronize cached present root allocationSize positive signedFits bounds race)

theorem retag_pointer_from_fields {K U C F A : Type} [DecidableEq K]
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
    (slice : SliceFacts projection choice place len)
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
  exact core_pointer_stage h budget value output place (retaggedPlace place id global.nextPointerTag) place.layout.ty
    (beforeTagState ambient frames frame borrowFrame global)
    (completedState ambient frames frame borrowFrame id entry rootTag global fresh capacity offset len)
    shape pointee policy construct
    (retag_place_from_fields h prepared access projection vtable pointers choice sources budget place
      ambient frames frame borrowFrame id entry capacity base offset len rootTag global fresh distinct rootUnprotected pointer frozen pointerWiring width
      globalKind globals extraWiring synchronize cached present root allocationSize positive signedFits bounds slice race)
    reconstruct



#print axioms reborrow_from_fields
#print axioms retag_place_from_fields
#print axioms retag_pointer_from_fields
end DuplicatePrefix.TypedRetagFields

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.TypedRetagFields.retag_pointer_from_fields,
      ``DuplicatePrefix.TypedRetagFields.retag_place_from_fields,
      ``DuplicatePrefix.TypedRetagFields.reborrow_from_fields] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
