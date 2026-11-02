import duplicate_prefix.S03IntegerCallResources
import duplicate_prefix.S03WildcardEmptyClassification

namespace DuplicatePrefix.S03WildcardMissCallResources
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Reuse only the initial numeric/runtime resource projection for the same
nonnull empty address. This does not identify integer and wildcard execution:
the actual wildcard call is proved separately by the miss adapters. -/
def numeric_contract {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : pointer.provenance = .wildcard) :
    ConsistentContract options limits remaining span before (.integer pointer.offset.bytes) 0 place := by
  have nonnull := (S03WildcardEmptyClassification.candidate input.contract wildcard).1
  refine ⟨{input.contract with reference := .empty rfl ?_,separated := Or.inl rfl},input.metadata⟩
  exact DuplicatePrefixEmptyReferenceInput.no_provenance_iff _ _ _ _ |>.mpr nonnull

def of_contract {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : pointer.provenance = .wildcard) :
    S03IntegerCallResources.Packet (numeric_contract input wildcard) :=
  S03IntegerCallResources.of_contract (numeric_contract input wildcard)

end
end DuplicatePrefix.S03WildcardMissCallResources
