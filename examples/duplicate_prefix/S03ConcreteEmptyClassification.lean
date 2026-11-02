import duplicate_prefix.ConcreteEmptyCandidateDispatch
import duplicate_prefix.S03ConcreteLiveCandidate
import duplicate_prefix.S03MaterializableInput
import duplicate_prefix.S05ConsistentCallSpecification

namespace DuplicatePrefix.S03ConcreteEmptyClassification
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification DuplicatePrefixEmptyReferenceInput S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- Initial live alternative at the original concrete allocation and parent.
Lookup, parent presence and runtime facts are derived by classification; they
are not extra successful-operation inputs to the caller contract. -/
structure Live {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (id : AllocId) (tag : BorTag) where
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  live : before.memory.live.find? (fun row => row.1 == id) = some (id,entry)
  base : UInt64
  cached : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  parent : UniIndex
  node : TreeNode
  tagged : entry.allocation.extra.indexOfTag tag = some parent
  present : entry.allocation.extra.nodeAt parent = some node
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra input.contract.destination.tracker.global
  nodeRoom : entry.allocation.extra.nodes.size+16 < 65536

/-- Exhaustive original Candidate alternatives: live backing with its actual
parent, supported nonlive rows, or the original lazy image with its derived
materialization packet. No resolver/retag/call success is an initial premise. -/
def Cases {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (id : AllocId) (tag : BorTag) : Prop :=
  Nonempty (Live input id tag) ∨
    (Metadata before.memory id (some tag) ∧ before.memory.live.find? (fun row => row.1 == id) = none) ∨
    (Materializable (imageContext options before input.contract.tracker) before.memory before.user.addresses id (some tag) ∧
      Nonempty (S03MaterializableInput.Packet options before input.contract.tracker id (some tag)))

theorem classify {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (id : AllocId) (tag : BorTag) (concrete : pointer.provenance = .concrete id tag) :
    pointer.offset.bytes ≠ 0 ∧ Cases input id tag := by
  have candidate : Candidate (imageContext options before input.contract.tracker)
      before.memory before.user.addresses pointer.withOptionalProvenance := by
    cases reference : input.contract.reference with
    | empty zero metadata => exact metadata
    | positive value encoding positive => have bad := positive.borrow.positive;contradiction
  simp only [Candidate,Pointer.withOptionalProvenance,concrete] at candidate
  refine ⟨candidate.1,?_⟩
  rcases ConcreteEmptyCandidateDispatch.target_cases _ _ _ id tag candidate.2.2 with live | nonlive | image
  · obtain ⟨entry,found,parent⟩ := live
    obtain ⟨nonnull,base,index,node,cached,tagged,present⟩ :=
      S03ConcreteLiveCandidate.parent input.contract id entry found tag concrete
    obtain ⟨runtime,room⟩ := S03ConcreteLiveCandidate.runtime input.contract id entry found
    exact Or.inl ⟨⟨entry,found,base,cached,index,node,tagged,present,runtime,room⟩⟩
  · exact Or.inr (Or.inl nonlive)
  · exact Or.inr (Or.inr ⟨image,S03MaterializableInput.of_input options before input.contract.tracker id (some tag)
      image input.contract.resources.cachedRootsBelow⟩)

end
end DuplicatePrefix.S03ConcreteEmptyClassification
