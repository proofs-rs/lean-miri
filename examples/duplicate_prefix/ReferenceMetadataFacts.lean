import duplicate_prefix.RootMetadataQueries
import Miri.Input.RuntimeArrayFacts

namespace DuplicatePrefix.ReferenceMetadataFacts
open Miri Miri.Input Miri.ABI Miri.Interpreter
open RootMetadataQueries
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def prepared : CompilerFactAdapters.Prepared :=
  PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts

theorem slice_tail_type : CompilerFacts.requiredType context 4 "metadata_tail" = .ok 4 := by
  unfold CompilerFacts.requiredType CompilerFacts.optionalType
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem slice_inhabited : CompilerFacts.boolean context 4 "opsem_inhabited" = .ok true := by
  unfold CompilerFacts.boolean
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

open Lean Elab Tactic in
elab "simp_adapter_source" : tactic => do
  let env ← getEnv
  let names ← ([".CompilerFactAdapters.source", ".CompilerFactAdapters.shape",
    ".CompilerFactAdapters.field"] : List String).mapM fun (suffix : String) => do
      let found := env.constants.toList.filterMap fun (name, _) =>
        if name.toString.endsWith suffix then some (mkIdent name) else none
      match found with
      | [name] => pure name
      | _ => throwError "expected exact source helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simp only [$[$names:ident],*]))

theorem slice_metadata_tail : CompilerFactAdapters.metadataTail prepared 4 = .ok .sliceOrStr := by
  unfold CompilerFactAdapters.metadataTail
  rw [show prepared.context = context from rfl]
  rw [slice_tail_type]
  simp_adapter_source
  simp only [context_node]
  with_unfolding_all rfl

theorem reference_kind : CompilerFactAdapters.validityKind prepared 3 = .ok (.reference true) := by
  unfold CompilerFactAdapters.validityKind
  simp_adapter_source
  rw [show prepared.context = context from rfl]
  simp only [context_node, mutable_slice_reference]
  with_unfolding_all rfl

theorem hooks_reference_kind (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks prepared base).classify choice 3 = pure (.reference true) := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  rw [reference_kind]
  with_unfolding_all rfl

theorem hooks_metadata_tail (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks prepared base).metadataTail choice 4 = pure .sliceOrStr := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  rw [slice_metadata_tail]
  with_unfolding_all rfl

theorem hooks_reference_name (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks prepared base).typeName choice 3 = pure "&mut [u8]" := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  simp_adapter_source
  rw [show prepared.context = context from rfl]
  simp only [context_node]
  with_unfolding_all rfl

theorem runtime_slice_inhabited (world : RuntimeArrayTypes.World) (fuel : Nat)
    (sameSource : context.runtime.matchesSourceLeft world.metadata.source.raw = true)
    (noConstructedSlice : world.entries.find? (·.value.ty == 4) = none) :
    RuntimeArrayFacts.opsemInhabited context world 4 (fuel+1) = .ok true := by
  unfold RuntimeArrayFacts.opsemInhabited
  rw [sameSource, noConstructedSlice]
  simp [slice_inhabited]

theorem prepared_slice_inhabited (source : PreparedContracts.SourceComparator) (fuel : Nat) :
    RuntimeArrayFacts.opsemInhabited context PreparedReflection.actual.prepared.types 4 (fuel+1) = .ok true := by
  apply runtime_slice_inhabited
  · rw [RuntimeMetadata.Indexed.matchesSourceLeft_eq]
    exact source.reflexive
  · rfl

#print axioms prepared_slice_inhabited

#print axioms hooks_reference_kind
#print axioms hooks_metadata_tail
#print axioms hooks_reference_name
#print axioms runtime_slice_inhabited

#print axioms slice_tail_type
#print axioms slice_inhabited
#print axioms slice_metadata_tail
#print axioms reference_kind
end DuplicatePrefix.ReferenceMetadataFacts
