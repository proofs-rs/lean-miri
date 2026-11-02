import duplicate_prefix.ReferenceMetadataFacts
import duplicate_prefix.TypedRetagFields
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace DuplicatePrefix.SharedReferenceMetadata
open Miri.Input Miri.Interpreter
open RootMetadataQueries

theorem shared_reference : CompilerFacts.referencePointee context 7 = .ok (4,.Not) := by
  unfold CompilerFacts.referencePointee
  simp_reference_query
  simp only [context_node]
  with_unfolding_all rfl

theorem shared_shape : CompilerFacts.retagTypeShape context 7 = .ok {} := by
  unfold CompilerFacts.retagTypeShape CompilerFacts.boolean
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem shared_kind : CompilerFactAdapters.validityKind ReferenceMetadataFacts.prepared 7 = .ok (.reference false) := by
  unfold CompilerFactAdapters.validityKind
  simp_adapter_source
  rw [show ReferenceMetadataFacts.prepared.context = context from rfl]
  simp only [context_node, shared_reference]
  with_unfolding_all rfl

theorem shared_dereference : CompilerFacts.builtinDeref context 7 true = .ok (some 4) := by
  unfold CompilerFacts.builtinDeref CompilerFacts.optionalType
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

noncomputable def sharedLayout : Miri.Interpreter.LocalLayout :=
  (PreparedReflection.actual.runtime.lookup 7).toOption.getD RootCompilerFacts.sliceLayout

theorem shared_layout_eq : PreparedReflection.actual.runtime.lookup 7 = .ok sharedLayout := by decide +kernel
theorem shared_layout_type : sharedLayout.ty = 7 := by decide +kernel
theorem shared_layout_sized : sharedLayout.layout.isSized = true := by decide +kernel
theorem shared_layout_readable : ∃ (pa pb : Miri.ABI.Primitive) (ra rb : Miri.ABI.WrappingRange)
    (offset : Miri.ABI.Size), sharedLayout.layout.backendRepr = .ScalarPair
      (a := .Initialized (value := pa) (validRange := ra))
      (b := .Initialized (value := pb) (validRange := rb)) (bOffset := offset) := by
  with_unfolding_all exact ⟨_, _, _, _, _, rfl⟩

theorem adapted_queries {K U C F A : Type} [DecidableEq K]
    (runtime : CompilerRuntimeQueries.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Miri.Memory.Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Miri.Memory.Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (base : TypedRetag.Hooks K (ValidityMachine.UserState U)) :
    let h := TypedValidityProviders.retagHooks ReferenceMetadataFacts.prepared runtime access projection vtable pointers choice base
    h.typeShape 7 = pure .reference ∧ h.referencePointee 7 = pure (4,.Not) ∧
      h.isUnpin 4 = pure true ∧ h.isUnsafeUnpin 4 = pure true ∧ h.typeIsFreeze 4 = pure true := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    simp only [TypedValidityProviders.retagHooks, CompilerFacts.typedRetagHooks, TypedMachineBindings.retagHooks]
    unfold_typed ".CompilerFacts.lift"
    simp only [show ReferenceMetadataFacts.prepared.context = context from rfl,
      shared_shape, shared_reference, RootMetadataQueries.slice_unpin,
      RootMetadataQueries.slice_unsafe_unpin, RootMetadataQueries.slice_freeze]
  all_goals rfl

theorem hooks_shared_kind (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks ReferenceMetadataFacts.prepared base).classify choice 7 =
      pure (.reference false) := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  rw [shared_kind]
  with_unfolding_all rfl

theorem hooks_shared_name (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks ReferenceMetadataFacts.prepared base).typeName choice 7 = pure "&[u8]" := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  simp_adapter_source
  rw [show ReferenceMetadataFacts.prepared.context = context from rfl]
  simp only [context_node]
  with_unfolding_all rfl

#print axioms shared_reference
#print axioms shared_shape
#print axioms shared_kind
end DuplicatePrefix.SharedReferenceMetadata

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.SharedReferenceMetadata.shared_reference,
      ``DuplicatePrefix.SharedReferenceMetadata.shared_shape,
      ``DuplicatePrefix.SharedReferenceMetadata.shared_kind,
      ``DuplicatePrefix.SharedReferenceMetadata.shared_dereference,
      ``DuplicatePrefix.SharedReferenceMetadata.shared_layout_eq,
      ``DuplicatePrefix.SharedReferenceMetadata.shared_layout_type,
      ``DuplicatePrefix.SharedReferenceMetadata.shared_layout_sized,
      ``DuplicatePrefix.SharedReferenceMetadata.shared_layout_readable,
      ``DuplicatePrefix.SharedReferenceMetadata.adapted_queries,
      ``DuplicatePrefix.SharedReferenceMetadata.hooks_shared_kind,
      ``DuplicatePrefix.SharedReferenceMetadata.hooks_shared_name] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved shared reference metadata dependency {dependency}"
