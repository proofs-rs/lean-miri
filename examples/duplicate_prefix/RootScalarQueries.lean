import duplicate_prefix.RootMetadataQueries
import duplicate_prefix.CanonicalConfigFacts

namespace DuplicatePrefix.RootScalarQueries
open Miri Miri.ABI Miri.Input Miri.Interpreter
set_option maxRecDepth 8192

open Lean Elab Tactic in
elab "unfold_scalar_leaves" : tactic => do
  let env ← getEnv
  let names ← ([".CompilerScalarLeaves.physical", ".CompilerScalarLeaves.lift"] : List String).mapM
    fun (suffix : String) => do
      let found := env.constants.toList.filterMap fun (name, _) =>
        if name.toString.endsWith suffix then some (mkIdent name) else none
      match found with
      | [name] => pure name
      | _ => throwError "expected source helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simp only [CompilerScalarLeaves.scalar, $[$names:ident],*]))

theorem usize_classification (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (limits : ExecutionMachine.Limits) :
    (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits)).classify () 5 =
        pure (.integer .usize) := by
  change (PreparedContracts.actualConfig options () remaining span).scalar.classify () 5 = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).scalar]
  unfold_scalar_leaves
  have query := RootMetadataQueries.usize_classification
  simp only [RootMetadataQueries.context] at query
  rw [query]

theorem bool_classification (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (limits : ExecutionMachine.Limits) :
    (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits)).classify () 0 =
        pure .boolean := by
  change (PreparedContracts.actualConfig options () remaining span).scalar.classify () 0 = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).scalar]
  unfold_scalar_leaves
  have query := RootMetadataQueries.bool_classification
  simp only [RootMetadataQueries.context] at query
  rw [query]

theorem bool_layout (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (limits : ExecutionMachine.Limits) :
    (ExecutionMachine.scalarHooks (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () remaining span) limits)).boolLayout () =
        pure RootCompilerFacts.boolLayout := by
  change (PreparedContracts.actualConfig options () remaining span).scalar.boolLayout () = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).scalar]
  unfold_scalar_leaves
  have query := RootMetadataQueries.bool_primitive_layout
  simp only [RootMetadataQueries.context] at query
  rw [query]

#print axioms usize_classification
#print axioms bool_classification
#print axioms bool_layout
end DuplicatePrefix.RootScalarQueries
