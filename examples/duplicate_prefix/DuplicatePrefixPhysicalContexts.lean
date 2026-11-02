import duplicate_prefix.PhysicalMachineWrite

namespace DuplicatePrefix.DuplicatePrefixPhysicalContexts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter

set_option autoImplicit false in
/-- Source-built physical dictionaries at the two actual call fuel levels.
The equalities describe configuration wiring, not successful memory accesses.
Callers need not supply independent write/validation contexts or width facts. -/
structure Contexts (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) where
  writeContext : PhysicalMachineWrite.Context
  validationContext : PhysicalMachineWrite.Context
  accessEq : (PreparedContracts.actualConfig options () remaining span).access = validationContext.access
  validationWidth : validationContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  validationRuntimeSize : validationContext.access.runtime.pointerSize = Size.ofBytes 8
  sameRuntime : validationContext.access.runtime.base = writeContext.access.runtime.base
  width : writeContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  runtimeWidth : writeContext.access.runtime.base.pointerWidth = .w64
  runtimeSize : writeContext.access.runtime.pointerSize = Size.ofBytes 8
  outerAccessEq : (PreparedContracts.actualConfig options () (remaining + 1) span).access = writeContext.access

/-- Both dictionaries and every legacy physical-context equality are derived
from the fixed source configuration builder. No prestate, operation-success or
arbitrary-history premise is needed. -/
theorem exists_contexts (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) : Nonempty (Contexts options remaining span) := by
  obtain ⟨validation, accessEq, validationArithmetic, validationAlign⟩ :=
    (CanonicalConfigFacts.actual_fields options () remaining span).canonicalCopy
  obtain ⟨write, outerAccessEq, writeArithmetic, writeAlign⟩ :=
    (CanonicalConfigFacts.actual_fields options () (remaining + 1) span).canonicalCopy
  have validationRuntime : validation.access.runtime = PreparedReflection.actual.runtime.target := by
    rw [←accessEq, CanonicalConfigFacts.actual_access_runtime]
  have writeRuntime : write.access.runtime = PreparedReflection.actual.runtime.target := by
    rw [←outerAccessEq, CanonicalConfigFacts.actual_access_runtime]
  refine ⟨⟨write, validation, accessEq, ?_, ?_, ?_, ?_, ?_, ?_, outerAccessEq⟩⟩
  · exact validationArithmetic.symm.trans (CanonicalConfigFacts.actual_arithmetic options () remaining span)
  · rw [validationRuntime]
    rfl
  · exact congrArg RuntimeTargetDataLayout.base (validationRuntime.trans writeRuntime.symm)
  · exact writeArithmetic.symm.trans (CanonicalConfigFacts.actual_arithmetic options () (remaining + 1) span)
  · rw [←outerAccessEq]
    exact CanonicalConfigFacts.actual_target_width options () (remaining + 1) span
  · rw [writeRuntime]
    rfl

/-- A canonical derived pair, available without new caller certificates.
Classical choice selects dictionaries already proved to exist; it assumes no
new safety or interpreter result. -/
noncomputable def canonical (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) : Contexts options remaining span :=
  Classical.choice (exists_contexts options remaining span)

end DuplicatePrefix.DuplicatePrefixPhysicalContexts
