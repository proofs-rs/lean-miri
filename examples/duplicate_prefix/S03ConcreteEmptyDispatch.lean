import duplicate_prefix.S03ConcreteEmptyClassification
import duplicate_prefix.S03NonliveContract
import duplicate_prefix.S03LiveEmptyComplete
import duplicate_prefix.S03SeparateLiveComplete

namespace DuplicatePrefix.S03ConcreteEmptyDispatch
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification DuplicatePrefixEmptyReferenceInput S05ConsistentCallSpecification
set_option autoImplicit false
noncomputable section

/-- The initial concrete family dispatches every supported nonlive argument
and every live argument with a concrete return to the original actual Result.
Only live arguments with wildcard returns and lazy images remain explicit
alternatives. They are initial-domain cases, not successful resolver/call
premises or a claim that their remaining obligations have been completed. -/
theorem dispatch {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (id : AllocId) (tag : BorTag) (concrete : pointer.provenance = .concrete id tag)
    (count : UInt64) :
    (Nonempty (S03ConcreteEmptyClassification.Live input id tag) ∧
      input.contract.destination.pointer.provenance = .wildcard) ∨
    (Materializable (imageContext options before input.contract.tracker) before.memory before.user.addresses id (some tag) ∧
      Nonempty (S03MaterializableInput.Packet options before input.contract.tracker id (some tag))) ∨
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  rcases (S03ConcreteEmptyClassification.classify input id tag concrete).2 with live | nonlive | image
  · obtain ⟨state⟩ := live
    cases provenance : input.contract.destination.pointer.provenance with
    | concrete returnId returnTag =>
      have binding := input.contract.destination.binding
      simp only [DuplicatePrefixReferenceInput.Binding,provenance] at binding
      have returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag :=
        provenance.trans (congrArg (fun id => Provenance.concrete id returnTag) binding.1)
      by_cases same : id = input.contract.destination.id
      · have argumentConcrete : pointer.provenance = .concrete input.contract.destination.id tag :=
          concrete.trans (congrArg (fun id => Provenance.concrete id tag) same)
        exact Or.inr (Or.inr (S03LiveEmptyComplete.complete input tag argumentConcrete returnTag returnConcrete count))
      · exact Or.inr (Or.inr (S03SeparateLiveComplete.complete input id state.entry state.live (Ne.symm same)
          tag concrete returnTag returnConcrete count))
    | wildcard => exact Or.inl ⟨⟨state⟩,rfl⟩
  · exact Or.inr (Or.inr (S03NonliveContract.complete input id tag concrete nonlive.1 nonlive.2 count))
  · exact Or.inr (Or.inl image)

end
end DuplicatePrefix.S03ConcreteEmptyDispatch
