import duplicate_prefix.S02AcceptedSharedFullSiteBothNode
import duplicate_prefix.S02SeparateDestinationGenericSharedLenLedger
import duplicate_prefix.S02SharedSiteTagMargin
import duplicate_prefix.S02PostLenMutableInput

namespace DuplicatePrefix.S02AcceptedPostLenMutableInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The real accepted positive call reaches the completed slice::len return
with the mutable parent borrowing input needed for the forthcoming as_mut_ptr
FnEntry. No success of that future operation is assumed here. -/
theorem after_len
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (countPositive : 0 < count.toNat) (within : count ≤ len/2) :
    ∃ (entry result : CompilerFrameContext.ActualFrame)
      (initial post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (finalTree : BorrowTree) (held : MachineHooks.BorrowState)
      (raw : GeneralBorrowRawFnEntry.Input finalTree held.global),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry initial) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] entry initial) (Storage.withCurrent #[] result post) ∧
      result.location = .mir ⟨3,0⟩ ∧
      post.memory = RetagEntry.updatedMemory initial.memory reference.id sourceEntry finalTree ∧
      post.borrowTracker = some held ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree held.global ∧
      raw.parentTag = reference.tracker.global.nextPointerTag ∧
      raw.offset = reference.offset ∧ raw.len = len := by
  obtain ⟨reference,tracker,sourceEntry,child,sourceRaw,entry,site,machine,actual,prefixTrace,
    body,identity,callee,located,size,noClocks,sourceCell,lenCell,exprCell,_allImmediate,
    tracked,live,rawTag,rawParent,rawOffset,rawLen,runtime,⟨both⟩,activity,
    ⟨parentNode,nodePresent,sameTag⟩⟩ :=
    S02AcceptedSharedFullSiteBothNode.actual_shared_full_site
      id tag address len count input nonempty different returnTag returnConcrete countPositive within
  have bothRaw : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra tracker.global.protectedTags
      (some sourceRaw.parent) (some sourceRaw.selected) sourceRaw.maximum reference.offset len := by
    simpa only [rawParent] using both
  have activeRaw : GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra sourceRaw.parent .Write
      reference.offset (reference.offset+len) := by
    simpa only [rawParent] using activity
  obtain ⟨result,post,finalTree,held,_sharedChild,lenTrace,_resultFrame,resultLocation,memory,postTracked,_mode,
    postRuntime,_read,⟨postBoth⟩,_postActive,graph,_ghost,_shallow,_race,_addresses,_types,_extras,
    _backend,_unchecked,_noGc,_fixed,_thread⟩ :=
    S02SeparateDestinationGenericSharedLenLedger.complete_at_site
      id tag address len count input nonempty different returnTag returnConcrete
      reference tracker sourceEntry sourceRaw entry site machine actual body identity callee located size noClocks
      sourceCell lenCell exprCell tracked live rawTag rawOffset rawLen runtime bothRaw activeRaw
  have initialMargin := S02SharedSiteTagMargin.at_actual_call id tag address len count input
    nonempty different returnTag returnConcrete tracker entry machine actual tracked
  have tagRoom : held.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change held.global.nextPointerTag.value.toNat < 18446744073709551615
    have growth := graph.tagCounter
    omega
  have postBothRaw : DuplicatePrefixBorrowAuthorization.Positive finalTree held.global.protectedTags
      (some sourceRaw.parent) (some sourceRaw.selected) sourceRaw.maximum sourceRaw.offset sourceRaw.len := by
    simpa only [rawOffset,rawLen] using postBoth
  obtain ⟨mutableRaw,tagEq,_parent,_selected,_maximum,offsetEq,lenEq⟩ :=
    S02PostLenMutableInput.from_graph sourceEntry.allocation.extra finalTree tracker held sourceRaw
      postRuntime parentNode (by simpa only [rawParent] using nodePresent) sameTag
      postBothRaw graph tagRoom
  have memoryInitial : (RootZeroCompleteState.tick options remaining span machine).memory = machine.memory :=
    (S02SeparateDestinationTickLedger.preserved options remaining span machine).1
  refine ⟨entry,result,machine,post,reference,sourceEntry,finalTree,held,mutableRaw,actual,
    SuccessfulTrace.append prefixTrace lenTrace,resultLocation,?_,postTracked,postRuntime,?_,?_,?_⟩
  · rw [memoryInitial] at memory
    exact memory
  · exact tagEq.trans rawTag
  · exact offsetEq.trans rawOffset
  · exact lenEq.trans rawLen

end
end DuplicatePrefix.S02AcceptedPostLenMutableInput

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02AcceptedPostLenMutableInput.after_len) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved accepted post-len mutable input dependency {dependency}"
