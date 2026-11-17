import duplicate_prefix.CanonicalConfigFacts
import duplicate_prefix.Bounds

namespace DuplicatePrefix.CanonicalCopyBound
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

set_option autoImplicit false in
/-- The two projection dictionaries receive the same constructor maximum.
This uses generic builder-field equations and does not evaluate compiler data. -/
theorem maximum_query_of_fields (compiler : CompilerProviders.Prepared)
    (image : AllocationImage.Imported) (options : EvalConfigurationCore.Options)
    (leaves : Machine.RootLeaves) (nested : Except StepError CanonicalConfigFacts.RootConfig)
    (config : CanonicalConfigFacts.RootConfig)
    (fields : CanonicalConfigFacts.Fields compiler image options leaves nested config) :
    CompilerExecutionBounds.maximum compiler.runtime.target = .ok config.projection.maxSizeOfVal := by
  obtain ⟨placeOptions,_,table,_,projection,_⟩ := fields.placeConstruction
  obtain ⟨sourceTable,maximum,query,dynamic⟩ := fields.projectionDynamic
  have same : config.projection.maxSizeOfVal = config.projection.dynamic.maxSizeOfVal := by
    rw [projection]
    rfl
  have value : config.projection.maxSizeOfVal = maximum := by
    rw [same,dynamic]
    rfl
  exact query.trans (congrArg Except.ok value.symm)

set_option autoImplicit false in
/-- Compute only the pointer-size query, with the target otherwise arbitrary. -/
theorem maximum_64 (target : RuntimeTargetDataLayout) (width : target.pointerSize = Size.ofBytes 8) :
    CompilerExecutionBounds.maximum target = .ok (Size.ofBytes 9223372036854775807) := by
  unfold CompilerExecutionBounds.maximum
  rw [width]
  rfl

set_option autoImplicit false in
theorem actual_maximum (options : EvalConfigurationCore.Options) (choice : Unit)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options choice remaining span).projection.maxSizeOfVal =
      Size.ofBytes 9223372036854775807 := by
  have fields := CanonicalConfigFacts.actual_fields options choice remaining span
  have arithmetic := fields.arithmetic.symm.trans (CanonicalConfigFacts.actual_arithmetic options choice remaining span)
  have width : PreparedReflection.actual.compiler.runtime.target.pointerSize = Size.ofBytes 8 :=
    congrArg Miri.Memory.PointerArithmetic.pointerSize arithmetic
  have query := maximum_query_of_fields _ _ _ _ _ _ fields
  exact Except.ok.inj (query.symm.trans (maximum_64 _ width))

set_option autoImplicit false in
/-- The Rust half-length guard alone puts the copy count within the 64-bit
interpreter maximum; no additional configuration or signed-length premise is
needed. -/
theorem guarded (options : EvalConfigurationCore.Options) (choice : Unit)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (len count : UInt64) (within : count ≤ len/2) :
    count ≤ (PreparedContracts.actualConfig options choice remaining span).projection.maxSizeOfVal.bytes := by
  have notGt : ¬ count > len/2 := by
    intro larger
    have low := UInt64.le_iff_toNat_le.mp within
    have high := UInt64.lt_iff_toNat_lt.mp larger
    omega
  have twice := DuplicatePrefix.usize_guard notGt
  have lengthBound : len.toNat < 2^64 := UInt64.toNat_lt_size len
  have countBound : count.toNat ≤ 9223372036854775807 := by omega
  rw [actual_maximum]
  change count ≤ (9223372036854775807 : UInt64)
  apply UInt64.le_iff_toNat_le.mpr
  exact countBound

end DuplicatePrefix.CanonicalCopyBound
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.CanonicalCopyBound.maximum_query_of_fields,
      ``DuplicatePrefix.CanonicalCopyBound.maximum_64,
      ``DuplicatePrefix.CanonicalCopyBound.actual_maximum,
      ``DuplicatePrefix.CanonicalCopyBound.guarded] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved canonical guarded copy maximum dependency {dependency}"
