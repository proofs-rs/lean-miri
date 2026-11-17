import duplicate_prefix.CurrentCallConversionFiniteFold
namespace DuplicatePrefix.CurrentCallConversionResourcesFrame
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 200000

/-- The converter uses canonical getAllocInfo sizes and metadata. A real
materialization with equal allocation-info queries therefore transports its
existing resources without reconstructing a whole initial-state invariant. -/
theorem memory (oldMemory newMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (addresses : GlobalAddressState) (ids : List AllocId) (charge : Nat)
    (infoEq : ∀id,newMemory.getAllocInfo id=oldMemory.getAllocInfo id)
    (resources : CurrentCallConversionFiniteFold.Resources oldMemory addresses ids charge) :
    CurrentCallConversionFiniteFold.Resources newMemory addresses ids charge := by
  have sizesEq : CurrentCallConversionInfoRows.sizes newMemory=CurrentCallConversionInfoRows.sizes oldMemory:=by
    funext id
    unfold CurrentCallConversionInfoRows.sizes
    rw [infoEq id]
  rcases resources with cached | ⟨generation,managed,aligned,limit,endBound⟩
  · exact Or.inl cached
  · refine Or.inr ⟨generation,?_,?_,limit,endBound⟩
    · rcases managed with ⟨ordered,apart,infoRows,generationEq,mode,cursor,frontier,holes,bounded,pairwise⟩
      constructor
      · exact ordered
      · rw [sizesEq];exact apart
      · intro row member
        obtain ⟨info,found,notDead,size⟩:=infoRows row member
        refine ⟨info,(infoEq row.allocId).trans found,notDead,?_⟩
        rw [sizesEq]
        exact size
      · exact generationEq
      · exact mode
      · exact cursor
      · rw [sizesEq];exact frontier
      · rw [sizesEq];exact holes
      · exact bounded
      · exact pairwise
    · intro needed
      apply aligned
      obtain ⟨id,member,uncached,info,found,notTypeId⟩:=needed
      exact ⟨id,member,uncached,info,(infoEq id).symm.trans found,notTypeId⟩
end DuplicatePrefix.CurrentCallConversionResourcesFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallConversionResourcesFrame" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved conversion resources-frame dependency {dependency}"
