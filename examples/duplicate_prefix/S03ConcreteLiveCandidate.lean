import duplicate_prefix.S03LiveEmptyContractData

namespace DuplicatePrefix.S03ConcreteLiveCandidate
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification DuplicatePrefixEmptyReferenceInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- A selected live concrete branch of the ORIGINAL Candidate supplies its
cached base and actual parent. The live lookup/id equality are dispatch facts;
no additional reference-validity or successful resolver premise is introduced. -/
theorem parent
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : Contract options limits remaining span before (.pointer pointer) 0 place)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (tag : BorTag) (concrete : pointer.provenance = .concrete id tag) :
    pointer.offset.bytes ≠ 0 ∧ ∃ base parent node,
      before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ ∧
      entry.allocation.extra.indexOfTag tag = some parent ∧ entry.allocation.extra.nodeAt parent = some node := by
  have candidate : Candidate (imageContext options before input.tracker) before.memory before.user.addresses pointer.withOptionalProvenance := by
    cases reference : input.reference with
    | empty zero metadata => exact metadata
    | positive value encoding positive => have bad:=positive.borrow.positive;contradiction
  simp only [Candidate,Pointer.withOptionalProvenance,concrete] at candidate
  obtain ⟨cached,metadata⟩ := candidate.2
  obtain ⟨base,cached⟩ := cached
  refine ⟨candidate.1,base,?_⟩
  rcases metadata with known | ⟨source,root,absent,_⟩
  · cases known with
    | live actual found parent =>
      have same : actual = entry := congrArg Prod.snd (Option.some.inj (found.symm.trans live))
      subst actual
      obtain ⟨index,node,tagged,present⟩ := parent
      exact ⟨index,node,cached,tagged,present⟩
    | functionRow absent _ => rw [live] at absent;contradiction
    | vaListRow absent _ _ => rw [live] at absent;contradiction
    | nondataGlobal _ absent _ _ _ _ => rw [live] at absent;contradiction
    | dead _ absent _ _ _ _ => rw [live] at absent;contradiction
  · rw [live] at absent
    contradiction

/-- Any selected initial live allocation receives its full runtime and numeric
margin directly from the original Contract, using the actual enabled tracker. -/
theorem runtime
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {argument : DuplicatePrefixSliceArgument.Argument} {place : MPlaceTy Provenance}
    (input : Contract options limits remaining span before argument 0 place)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra input.destination.tracker.global ∧
    entry.allocation.extra.nodes.size+16 < 65536 := by
  have same : input.tracker=input.destination.tracker := Option.some.inj (input.runtime.enabled.symm.trans input.destination.enabled)
  have member : (id,entry) ∈ before.memory.live.toList := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live)
  have current : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra input.tracker.global :=
    ⟨input.runtime.formed _ member,input.runtime.coherent _ member,input.runtime.possible _ member,input.resources.tagsBelow _ member⟩
  rw [same] at current
  exact ⟨current,input.resources.nodeRoom _ member⟩

end
end DuplicatePrefix.S03ConcreteLiveCandidate
