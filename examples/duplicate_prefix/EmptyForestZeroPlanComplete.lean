import duplicate_prefix.GenericRootZeroPhysical

namespace DuplicatePrefix.EmptyForestZeroPlanComplete
open Lean Elab in
elab "empty_forest_zero_complete_source" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GenericRootZeroPhysical.complete_of_plan" then some name else none
  let [name] := names | throwError "expected the fixed generic zero-count Plan theorem"
  Lean.Meta.mkConstWithFreshMVarLevels name

/-- Re-export the existing kernel-checked zero branch theorem with its exact
StackPopRelease.Plan contract. This preserves every runtime, physical return,
trace and NoUB condition; it adds no assumed operation success to a final
invocation contract. Invokers must derive the Plan from their initial data. -/
abbrev complete := empty_forest_zero_complete_source

end DuplicatePrefix.EmptyForestZeroPlanComplete
