import duplicate_prefix.CurrentCallOrdinarySafety
import duplicate_prefix.CurrentCallOrdinaryWitness

/-! Apply the original strong Result to the concrete CURRENT/CURRENT witness.
The count is nonzero and satisfies the accepted-copy guard. The same fixed
metadata contracts remain explicit; this adds no Rust-history claim or proof
that the returned Bool has a particular value. -/
namespace DuplicatePrefix.CurrentCallOrdinaryWitness
open Miri Miri.Input
set_option autoImplicit false

theorem positive_result (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (sourceMatches : (PreparedReflection.actual.runtime.source.raw == PreparedReflection.actual.runtime.source.raw)=true) :
    DuplicatePrefixArgumentCallResult.Result options limits budget span before
      (.pointer source.value) 2 1 place :=
  CurrentCallOrdinarySafety.invoke (input span cmp sourceMatches) 1

theorem copy_guard : (1 : UInt64) ≠ 0 ∧ (1 : UInt64) ≤ (2 : UInt64)/2 := by decide +kernel

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallOrdinaryWitness." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved concrete witness safety dependency {name}: {dependency}"

#print axioms positive_result
end DuplicatePrefix.CurrentCallOrdinaryWitness
