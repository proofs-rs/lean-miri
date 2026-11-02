import duplicate_prefix.S05PriorCellLayouts
import duplicate_prefix.TypedRetagFields

/-! Compiler-query leaves for the auxiliary catalog, installed through the
actual production adapter.  There is no replacement of running metadata here
and no claim that the auxiliary and duplicate_prefix local IDs coincide. -/
namespace DuplicatePrefix.S05ZeroCellMetadataWitness
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem shared_queries {K U C F A : Type} [DecidableEq K]
    (runtime : CompilerRuntimeQueries.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (base : TypedRetag.Hooks K (ValidityMachine.UserState U)) :
    let h := TypedValidityProviders.retagHooks PriorCellMetadata.facts runtime access projection vtable pointers choice base
    h.typeShape 6 = pure .reference ∧
    h.referencePointee 6 = pure (2,.Not) ∧
    h.isUnpin 2 = pure true ∧
    h.isUnsafeUnpin 2 = pure true ∧
    h.typeIsFreeze 2 = pure false := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals
    simp only [TypedValidityProviders.retagHooks, CompilerFacts.typedRetagHooks, TypedMachineBindings.retagHooks]
    unfold_typed ".CompilerFacts.lift"
    simp only [PriorCellMetadata.shared_shape, PriorCellMetadata.shared_pointee,
      PriorCellMetadata.cell_unpin, PriorCellMetadata.cell_unsafe_unpin, PriorCellMetadata.cell_nonfreeze]
theorem slice_queries {K U C F A : Type} [DecidableEq K]
    (runtime : CompilerRuntimeQueries.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (base : TypedRetag.Hooks K (ValidityMachine.UserState U)) :
    let h := TypedValidityProviders.retagHooks PriorCellMetadata.facts runtime access projection vtable pointers choice base
    h.typeShape 7 = pure .reference ∧
    h.referencePointee 7 = pure (8,.Mut) ∧
    h.isUnpin 8 = pure true ∧
    h.isUnsafeUnpin 8 = pure true ∧
    h.typeIsFreeze 8 = pure true := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals
    simp only [TypedValidityProviders.retagHooks, CompilerFacts.typedRetagHooks, TypedMachineBindings.retagHooks]
    unfold_typed ".CompilerFacts.lift"
    simp only [PriorCellMetadata.slice_reference_shape, PriorCellMetadata.slice_pointee,
      PriorCellMetadata.slice_unpin, PriorCellMetadata.slice_unsafe_unpin, PriorCellMetadata.slice_freeze]

end DuplicatePrefix.S05ZeroCellMetadataWitness

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ZeroCellMetadataWitness." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved correlated metadata-witness dependency {dependency}"
