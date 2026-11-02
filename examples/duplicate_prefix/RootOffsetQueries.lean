import duplicate_prefix.TupleCandidates
namespace DuplicatePrefix.RootOffsetQueries
open Miri Miri.ABI Miri.Input Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem bool_kind : RootMetadataQueries.context.runtime.findKind .bool =
    RuntimeMetadata.lookup RootMetadataQueries.context.runtime 0 := by
  apply TupleCandidates.find_kind_of_projection
  · decide +kernel
  · decide +kernel

noncomputable def overflowLayout : LocalLayout :=
  (PreparedReflection.actual.runtime.layouts.find? (·.1 == 205)).getD (205, .error (.unknownType 205)) |>.2.toOption.getD RootCompilerFacts.usizeLayout

theorem overflow_lookup : RuntimeMetadata.lookup RootMetadataQueries.context.runtime 205 = .ok overflowLayout := by
  with_unfolding_all rfl

theorem bool_lookup : RuntimeMetadata.lookup RootMetadataQueries.context.runtime 0 = .ok RootCompilerFacts.boolLayout := by
  with_unfolding_all rfl

theorem overflow_layout :
    RootMetadataQueries.context.runtime.overflowTupleLayout RootCompilerFacts.usizeLayout = .ok overflowLayout := by
  unfold RuntimeMetadata.overflowTupleLayout
  rw [bool_kind, bool_lookup]
  simp only [bind, Except.bind]
  have ty : RootCompilerFacts.boolLayout.ty = 0 := by with_unfolding_all rfl
  have usizety : RootCompilerFacts.usizeLayout.ty = 5 := by with_unfolding_all rfl
  rw [ty, TupleCandidates.tuple_eq, usizety, TupleCandidates.actual_candidates]
  simp only [bind, Except.bind]
  exact overflow_lookup

theorem destination_classification :
    CompilerExecutionProviders.scalarClass RootMetadataQueries.context 8 = .ok .pointer := by
  simp_execution_query
  simp only [RootMetadataQueries.context_node]
  with_unfolding_all rfl

theorem overflow_query (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options () remaining span).scalar.overflowLayout ()
      RootCompilerFacts.usizeLayout = pure overflowLayout := by
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).scalar]
  unfold_scalar_leaves
  have query := overflow_layout
  simp only [RootMetadataQueries.context] at query
  rw [query]
  rfl

#print axioms overflow_layout
#print axioms destination_classification
#print axioms overflow_query
end DuplicatePrefix.RootOffsetQueries
