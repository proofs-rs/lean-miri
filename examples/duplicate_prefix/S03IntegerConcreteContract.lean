import duplicate_prefix.S03IntegerZeroContract
import duplicate_prefix.S03IntegerPositiveContract

namespace DuplicatePrefix.S03IntegerConcreteContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
noncomputable section

/-- The revised specification for integer/NoProv empty arguments and concrete
return destinations, for every UInt64 count. Each branch executes the original
call, body and Return; the output is the original public safety result. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {address : UInt64}
    {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.integer address) 0 place)
    (tag : BorTag) (concrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id tag)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.integer address) 0 count place := by
  by_cases zero : count = 0
  · subst count
    exact S03IntegerZeroContract.complete input tag concrete
  · exact S03IntegerPositiveContract.complete input tag concrete count zero

end
end DuplicatePrefix.S03IntegerConcreteContract
