import duplicate_prefix.S05PriorCellPrepared
import duplicate_prefix.LayoutLookupProof
namespace DuplicatePrefix.PriorCellMetadata
open Lean Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
/-- These facts describe this auxiliary catalog only. They do not execute
`prior_context`, establish caller validity, or change fixed call metadata. -/
noncomputable def facts : CompilerFactAdapters.Prepared :=
  actual.compiler.lifecycle.calls.symbols.facts
private def checkedOk {Error Value : Type} : (result : Except Error Value) → result.isOk = true → Value
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)

theorem context_runtime : facts.context.runtime.toRuntimeMetadata = actual.runtime := by rfl

theorem compiler_layout_lookup (id : TypeId) :
    CompilerFacts.layoutOf facts.context id = (actual.runtime.lookup id).mapError toString := by
  unfold CompilerFacts.layoutOf
  have query : facts.context.runtime.lookup id = facts.context.runtime.toRuntimeMetadata.lookup id :=
    LayoutLookupProof.indexed_lookup_eq _ none id
  rw [query, context_runtime]

theorem context_node (id : TypeId) :
    facts.context.runtime.node id = facts.context.runtime.toRuntimeMetadata.node id := by
  exact NodeLookupProof.indexed_node _ id none

open Lean Elab Tactic in
elab "unfold_prior_fact_helpers" : tactic => do
  let names ← ([".CompilerFacts.facts", ".CompilerFacts.node", ".CompilerFacts.shape",
    ".CompilerFacts.typeRef", ".CompilerFacts.string", ".CompilerFacts.field"] : List String).mapM fun (suffix : String) => do
    let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some (mkIdent name) else none
    match found with
    | [name] => pure name
    | _ => throwError "expected unique compiler fact helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simp only [$[$names:ident],*]))

theorem cell_layout_supported : (actual.runtime.lookup 2).isOk = true := by decide +kernel
noncomputable def cellLayout : LocalLayout :=
  checkedOk (actual.runtime.lookup 2) cell_layout_supported

theorem cell_layout_query : CompilerFacts.layoutOf facts.context 2 = .ok cellLayout := by
  unfold CompilerFacts.layoutOf
  have query : facts.context.runtime.lookup 2 = facts.context.runtime.toRuntimeMetadata.lookup 2 :=
    LayoutLookupProof.indexed_lookup_eq _ none 2
  rw [query]
  decide +kernel

theorem cell_geometry : cellLayout.layout.isSized = true ∧
    cellLayout.layout.size = Size.ZERO ∧ cellLayout.layout.align.abi = Align.ONE := by
  decide +kernel

theorem cell_nonfreeze : CompilerFacts.boolean facts.context 2 "is_freeze" = .ok false := by
  unfold CompilerFacts.boolean
  unfold_prior_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem cell_unpin : CompilerFacts.boolean facts.context 2 "is_unpin" = .ok true := by
  unfold CompilerFacts.boolean
  unfold_prior_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem cell_unsafe_unpin : CompilerFacts.boolean facts.context 2 "is_unsafe_unpin" = .ok true := by
  unfold CompilerFacts.boolean
  unfold_prior_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem shared_shape : CompilerFacts.retagTypeShape facts.context 6 = .ok .reference := by
  unfold CompilerFacts.retagTypeShape CompilerFacts.boolean
  unfold_prior_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem shared_pointee : CompilerFacts.referencePointee facts.context 6 = .ok (2,.Not) := by
  unfold CompilerFacts.referencePointee
  unfold_prior_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem shared_deref : CompilerFacts.builtinDeref facts.context 6 true = .ok (some 2) := by
  unfold CompilerFacts.builtinDeref CompilerFacts.optionalType
  unfold_prior_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem slice_pointee : CompilerFacts.referencePointee facts.context 7 = .ok (8,.Mut) := by
  unfold CompilerFacts.referencePointee
  unfold_prior_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

end DuplicatePrefix.PriorCellMetadata
