import duplicate_prefix.ScalarValidityQueries
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace DuplicatePrefix.WideValidityQueries
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ScalarValidityQueries
theorem slice_unsized : CompilerFacts.boolean
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context 4 "is_sized" = .ok false := by
  unfold CompilerFacts.boolean
  unfold_fact_helpers
  have node : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 4 =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node 4 :=
    RootMetadataQueries.context_node 4
  simp only [node]
  with_unfolding_all rfl
theorem raw_slice_kind : CompilerFactAdapters.validityKind
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts 154 = .ok (.rawPointer 4 false) := by
  unfold CompilerFactAdapters.validityKind
  unfold_raw_validity_helpers
  dsimp only
  have nodes (id : TypeId) : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node id =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node id :=
    RootMetadataQueries.context_node id
  simp only [nodes]
  change (do
    let sized ← CompilerFacts.boolean PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context 4 "is_sized"
    pure (ValidityVisitor.TypeKind.rawPointer 4 sized)) = .ok (ValidityVisitor.TypeKind.rawPointer 4 false)
  rw [slice_unsized]
  rfl
theorem hooks_raw_slice_kind (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).classify
      choice 154 = pure (.rawPointer 4 false) := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  rw [raw_slice_kind]
  with_unfolding_all rfl

theorem hooks_raw_slice_name (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).typeName
      choice 154 = pure "*const [u8]" := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  unfold_validity_source
  have node : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 154 =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node 154 :=
    RootMetadataQueries.context_node 154
  rw [node]
  with_unfolding_all rfl

theorem slice_metadata_tail : CompilerFactAdapters.metadataTail
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts 4 = .ok .sliceOrStr := by
  unfold CompilerFactAdapters.metadataTail CompilerFacts.requiredType CompilerFacts.optionalType
  unfold_fact_helpers
  unfold_validity_source
  have nodes (id : TypeId) : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node id =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node id :=
    RootMetadataQueries.context_node id
  simp only [nodes]
  with_unfolding_all rfl

theorem hooks_slice_metadata_tail (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).metadataTail
      choice 4 = pure .sliceOrStr := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  rw [slice_metadata_tail]
  with_unfolding_all rfl

open Lean Elab Command in
run_cmd do
  for declaration in [``slice_metadata_tail, ``hooks_slice_metadata_tail, ``slice_unsized, ``raw_slice_kind, ``hooks_raw_slice_kind, ``hooks_raw_slice_name] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.WideValidityQueries
