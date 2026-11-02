import duplicate_prefix.S03IntegerContract
import duplicate_prefix.S03ConcreteContract
import duplicate_prefix.S03WildcardContract

namespace DuplicatePrefix.S03EmptyContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
noncomputable section

/-- Every empty argument representation and every count/return-provenance
case in the explicit consistent initial domain satisfies the original actual
call Result. Candidate classification, initialization, body and Return are
proved internally; no branch-success callback or safety premise is assumed.
This is the len=0 theorem. Positive lengths, ordinary-valid-input coverage,
and the original unrefined Contract/Target remain separate obligations. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before argument 0 place)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument 0 count place := by
  cases argument with
  | integer address => exact S03IntegerContract.complete input count
  | pointer pointer =>
    cases provenance : pointer.provenance with
    | concrete id tag => exact S03ConcreteContract.complete input id tag provenance count
    | wildcard => exact S03WildcardContract.complete input provenance count

end
end DuplicatePrefix.S03EmptyContract
