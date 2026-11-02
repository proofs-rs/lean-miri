import duplicate_prefix.S02ConcreteReturnAllCountResult
import duplicate_prefix.S02WildcardReturnAllCountResult

namespace DuplicatePrefix.S06ConsistentContractSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open DuplicatePrefixCallSpecification
set_option autoImplicit false
noncomputable section

/-- The unchanged consistent call contract entails the original actual-call
Result for every argument representation, length and count. Provenance,
allocation relation and all execution branches are classified internally.
This is contract safety, not coverage of all ordinary valid inputs. -/
theorem invoke
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {place : MPlaceTy Provenance}
    (len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      argument len place) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  cases provenance : input.contract.destination.pointer.provenance with
  | concrete supplied tag =>
    have binding := input.contract.destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
    have sameId : supplied = input.contract.destination.id := binding.1
    have concrete : input.contract.destination.pointer.provenance =
        .concrete input.contract.destination.id tag := by
      simpa only [sameId] using provenance
    exact S02ConcreteReturnAllCountResult.result len count input tag concrete
  | wildcard =>
    exact S02WildcardReturnAllCountResult.result len count input provenance

/-- Discharge the existing target, preserving its original Result conclusion. -/
theorem target : S05ConsistentCallSpecification.Target := by
  intro options limits remaining span before argument len place input count
  exact invoke len count input

end
end DuplicatePrefix.S06ConsistentContractSafety

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S06ConsistentContractSafety." then
      for dependency in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved final consistent contract safety dependency {dependency}"
