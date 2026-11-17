import duplicate_prefix.S03MaterializableConcreteContract
import duplicate_prefix.S03MaterializableWildcardReturnContract

namespace DuplicatePrefix.S03MaterializableConcreteAllReturns
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Original every-count Result for concrete incoming materializable MEMORY
or supported STATIC empty references, for BOTH return provenances. The original
image candidate retains finite relocation support; the actual lazy preparation
is composed without constructing a new Contract or renewing its work budget. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (id : AllocId) (parentTag : BorTag) (concrete : pointer.provenance = .concrete id parentTag)
    (candidate : DuplicatePrefixEmptyReferenceInput.Materializable (imageContext options before input.contract.tracker)
      before.memory before.user.addresses id (some parentTag))
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  cases provenance : input.contract.destination.pointer.provenance with
  | concrete supplied tag =>
    have binding := input.contract.destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
    have actual : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id tag :=
      provenance.trans (congrArg (fun value => Provenance.concrete value tag) binding.1)
    exact S03MaterializableConcreteContract.complete input id parentTag concrete candidate tag actual count
  | wildcard =>
    exact S03MaterializableWildcardReturnContract.complete input id parentTag concrete candidate provenance count

end
end DuplicatePrefix.S03MaterializableConcreteAllReturns
