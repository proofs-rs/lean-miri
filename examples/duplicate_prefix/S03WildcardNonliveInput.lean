import duplicate_prefix.S03WildcardEmptyClassification
import duplicate_prefix.S03NonliveMetadataTag
import duplicate_prefix.S03NonliveCallResources

namespace DuplicatePrefix.S03WildcardNonliveInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification DuplicatePrefixEmptyReferenceInput S05ConsistentCallSpecification
set_option autoImplicit false
noncomputable section

def concretePointer (pointer : Pointer Provenance) (id : AllocId) (tag : BorTag) : Pointer Provenance :=
  Pointer.new (.concrete id tag) (Size.ofBytes pointer.offset.bytes)

/-- A selected nonlive wildcard hit supplies a same-state concrete candidate.
This changes only the first argument representation; the actual call equality
is proved separately before transporting any execution/safety result. -/
def concrete_input {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : pointer.provenance = .wildcard)
    (hit : S03WildcardEmptyClassification.Hit (imageContext options before input.contract.tracker)
      before.memory before.user.addresses pointer.offset.bytes)
    (metadata : Metadata before.memory hit.id none)
    (absent : before.memory.live.find? (fun row => row.1 == hit.id) = none)
    (tag : BorTag) :
    ConsistentContract options limits remaining span before (.pointer (concretePointer pointer hit.id tag)) 0 place := by
  have nonnull := (S03WildcardEmptyClassification.candidate input.contract wildcard).1
  have parentMetadata := S03NonliveMetadataTag.changeTag before.memory hit.id none (some tag) metadata absent
  refine ⟨{input.contract with reference := .empty rfl ?_,separated := Or.inl rfl},input.metadata⟩
  exact ⟨nonnull,⟨⟨hit.base,hit.cached⟩,Or.inl parentMetadata⟩⟩

end
end DuplicatePrefix.S03WildcardNonliveInput
