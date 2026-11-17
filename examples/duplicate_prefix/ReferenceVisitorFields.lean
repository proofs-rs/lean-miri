import duplicate_prefix.ReferenceValidity
import duplicate_prefix.TypedRetagFields

/-! Exact source callback identities for the reference validity visitor. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.ReferenceVisitorFields
open Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter

theorem typed_reference_fields {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (base : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat) :
    let hooks := TypedValidityProviders.visitor prepared runtime access allocation compiler pointers retag budget base
    ∃ inner : ValidityMachine.Compiler K U C,
      inner.debugAssertions = compiler.debugAssertions ∧
      inner.debugAbiCheck = compiler.debugAbiCheck ∧
      hooks.toOp = (fun c place => placeToOp (ValidityMachine.placeHooks access allocation
        (ValidityMachine.compilerPolicy inner)) c place) ∧
      hooks.readImmediate = (fun c place expected => do
        let op ← placeToOp (ValidityMachine.placeHooks access allocation
          (ValidityMachine.compilerPolicy inner)) c place
        ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access) op expected) ∧
      hooks.writeNoValidate = (fun c value destination => do
        let validate ← ValidityMachine.enforceValidity
        ValidityMemory.writeNoValidate (ValidityMachine.memoryEnvironment access)
          (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy inner)) c
          (fun _ => validate) value destination) ∧
      hooks.ptrToPlace = PointerPlaceMachine.fromImmediate access
        (CompilerExecutionProviders.pointerCompiler prepared) ∧
      hooks.checkPointerAccess = (fun _ => ValidityMachine.checkPointerAccessResult access) ∧
      hooks.checkPointerAlignResult = (fun _ => ValidityMachine.checkPointerAlignResult access) ∧
      hooks.scalarMayBeNull = (fun _ => ValidityMachine.scalarMayBeNull) ∧
      hooks.withGhostValidation (A := ValidityVisitor.Session Provenance) =
        @ValidityMachine.withGhostValidation K U (ValidityVisitor.Session Provenance) ∧
      hooks.retagPointer = (fun choice value ty => TypedRetag.machineRetagPtrValue
        (TypedValidityProviders.retagHooks prepared runtime access hooks.projection hooks.vtable
          pointers choice retag) budget value ty) := by
  refine ⟨PointerPlaceMachine.bindCompiler access allocation
    (CompilerExecutionProviders.pointerCompiler prepared)
    (PlaceDynamic.withVTable base.projection.dynamic base.vtable) base.vtable
    base.projection.dynamicFuel compiler, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem typed_reference_metadata {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (base : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat) :
    let hooks := TypedValidityProviders.visitor prepared runtime access allocation compiler pointers retag budget base
    hooks.target = base.target ∧
    hooks.classify = (CompilerFactAdapters.validityHooks prepared base).classify ∧
    hooks.typeName = (CompilerFactAdapters.validityHooks prepared base).typeName ∧
    hooks.metadataTail = (CompilerFactAdapters.validityHooks prepared base).metadataTail ∧
    hooks.opsemInhabited = (CompilerFactAdapters.validityHooks prepared base).opsemInhabited ∧
    hooks.sizeAndAlign = (fun choice place => DynamicLayout.sizeAndAlignFromMeta
      (PlaceDynamic.withVTable base.projection.dynamic base.vtable) choice base.projection.dynamicFuel
      place.mplace.metadata place.layout) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms typed_reference_metadata

#print axioms typed_reference_fields
end DuplicatePrefix.ReferenceVisitorFields
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ReferenceVisitorFields.typed_reference_fields,
      ``DuplicatePrefix.ReferenceVisitorFields.typed_reference_metadata] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved reference visitor dependency {dependency}"
