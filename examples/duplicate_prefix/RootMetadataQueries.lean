import duplicate_prefix.NodeLookupProof
import duplicate_prefix.RootCompilerFacts

namespace DuplicatePrefix.RootMetadataQueries
open Miri Miri.Input Miri.ABI Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def context : CompilerFacts.Context :=
  PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context

theorem context_node (id : TypeId) :
    context.runtime.node id = context.runtime.toRuntimeMetadata.node id := by
  exact NodeLookupProof.indexed_node _ id none

open Lean Elab Tactic in
elab "unfold_fact_helpers" : tactic => do
  let env ← getEnv
  let names ← ([".CompilerFacts.facts", ".CompilerFacts.node"] : List String).mapM
    fun (suffix : String) => do
      let found := env.constants.toList.filterMap fun (name, _) =>
        if name.toString.endsWith suffix then some (mkIdent name) else none
      match found with
      | [name] => pure name
      | _ => throwError "expected source helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| unfold $[$names:ident]*))

theorem source_pointer_pointee : CompilerFacts.builtinDeref context 9 true = .ok (some 1) := by
  unfold CompilerFacts.builtinDeref CompilerFacts.optionalType
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem destination_pointer_pointee : CompilerFacts.builtinDeref context 8 true = .ok (some 1) := by
  unfold CompilerFacts.builtinDeref CompilerFacts.optionalType
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem slice_freeze : CompilerFacts.boolean context 4 "is_freeze" = .ok true := by
  unfold CompilerFacts.boolean
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem slice_unpin : CompilerFacts.boolean context 4 "is_unpin" = .ok true := by
  unfold CompilerFacts.boolean
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem slice_unsafe_unpin : CompilerFacts.boolean context 4 "is_unsafe_unpin" = .ok true := by
  unfold CompilerFacts.boolean
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem byte_freeze : CompilerFacts.boolean context 1 "is_freeze" = .ok true := by
  unfold CompilerFacts.boolean
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl


open Lean Elab Tactic in
elab "simp_reference_query" : tactic => do
  let env ← getEnv
  let names ← ([".CompilerFacts.node", ".CompilerFacts.shape", ".CompilerFacts.typeRef",
    ".CompilerFacts.string", ".CompilerFacts.field"] : List String).mapM fun (suffix : String) => do
    let found := env.constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some (mkIdent name) else none
    match found with
    | [name] => pure name
    | _ => throwError "expected exact source helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simp only [$[$names:ident],*]))

theorem mutable_slice_reference : CompilerFacts.referencePointee context 3 = .ok (4,.Mut) := by
  unfold CompilerFacts.referencePointee
  simp_reference_query
  simp only [context_node]
  with_unfolding_all rfl

theorem mutable_slice_dereference : CompilerFacts.builtinDeref context 3 true = .ok (some 4) := by
  unfold CompilerFacts.builtinDeref CompilerFacts.optionalType
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl


open Lean Elab Tactic in
elab "simp_execution_query" : tactic => do
  let env ← getEnv
  let names ← ([".CompilerExecutionProviders.node", ".CompilerExecutionProviders.metadata"] : List String).mapM
    fun (suffix : String) => do
      let found := env.constants.toList.filterMap fun (name, _) =>
        if name.toString.endsWith suffix then some (mkIdent name) else none
      match found with
      | [name] => pure name
      | _ => throwError "expected exact source helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simp only [CompilerExecutionProviders.scalarClass,
    CompilerExecutionProviders.integerKind, $[$names:ident],*]))

theorem usize_classification : CompilerExecutionProviders.scalarClass context 5 = .ok (.integer .usize) := by
  simp_execution_query
  simp only [context_node]
  with_unfolding_all rfl

theorem bool_classification : CompilerExecutionProviders.scalarClass context 0 = .ok .boolean := by
  simp_execution_query
  simp only [context_node]
  with_unfolding_all rfl

theorem bool_primitive_layout : context.primitiveLayout "bool" = .ok RootCompilerFacts.boolLayout := by
  with_unfolding_all rfl

theorem mutable_slice_shape : CompilerFacts.retagTypeShape context 3 = .ok {} := by
  unfold CompilerFacts.retagTypeShape CompilerFacts.boolean
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem usize_retag_shape : CompilerFacts.retagTypeShape context 5 =
    .ok {isReference := false} := by
  unfold CompilerFacts.retagTypeShape CompilerFacts.boolean
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

open Lean Elab Command in
run_cmd do
  for name in #[``context_node, ``source_pointer_pointee, ``destination_pointer_pointee,
      ``slice_freeze, ``slice_unpin, ``slice_unsafe_unpin, ``byte_freeze,
      ``mutable_slice_reference, ``mutable_slice_dereference, ``mutable_slice_shape,
      ``usize_classification, ``bool_classification, ``bool_primitive_layout, ``usize_retag_shape] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{name} depends on unapproved axiom {dependency}"

#print axioms context_node
#print axioms source_pointer_pointee
end DuplicatePrefix.RootMetadataQueries
