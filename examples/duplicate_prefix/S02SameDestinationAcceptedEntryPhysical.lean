import duplicate_prefix.S02SameDestinationZeroCore
import duplicate_prefix.S02SameDestinationAcceptedEntryResources


namespace DuplicatePrefix.S02SameDestinationAcceptedEntryPhysical
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Numeric source prerequisites hold for the source row in the actual installed call. -/
theorem at_actual_call
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (tracker : MachineHooks.BorrowState)
    (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (installed : CompilerFrameContext.ActualFrame)
    (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed post))
    (tracked : post.borrowTracker = some tracker)
    (live : post.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry)) :
    sourceEntry.allocation.byteSize = reference.entry.allocation.byteSize ∧
    sourceEntry.allocation.len = reference.entry.allocation.len ∧
    sourceEntry.allocation.len = sourceEntry.allocation.byteSize.bytes.toNat ∧
    sourceEntry.allocation.mutability = .Mut ∧
    sourceEntry.allocation.len+64 < 18446744073709551616 ∧
    tracker.global.nextPointerTag.value.toNat = reference.tracker.global.nextPointerTag.value.toNat+2 := by
  obtain ⟨other,otherTracker,otherFrame,otherPost,otherEntry,_child,otherRaw,otherActual,otherTracked,
      otherLive,_tag,_parent,rawOffset,rawLen,_runtime,_activity,nodes,nodeUInt,tagRoom,_both,capacity,sizeEq,lenEq,mutable,counter⟩ :=
    S02SameDestinationAcceptedEntryResources.after_exact id tag address len count input nonempty sameAllocation returnTag returnConcrete
  have same : Storage.withCurrent #[] otherFrame otherPost = Storage.withCurrent #[] installed post :=
    (EStateM.Result.ok.inj (otherActual.symm.trans actual)).2
  have postEq : otherPost = post := congrArg (fun s : RootState => s.machine) same
  have idEq : other.id = reference.id := by
    have h1 := other.binding
    have h2 := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at h1 h2
    exact h1.1.symm.trans h2.1
  have entryEq : other.entry = reference.entry := by
    have h := other.live
    rw [idEq] at h
    exact congrArg Prod.snd (Option.some.inj (h.symm.trans reference.live))
  have currentEq : otherEntry = sourceEntry := by
    have h := otherLive
    rw [postEq,idEq] at h
    exact congrArg Prod.snd (Option.some.inj (h.symm.trans live))
  have trackerEq : otherTracker = tracker :=
    Option.some.inj (by rw [postEq] at otherTracked; exact otherTracked.symm.trans tracked)
  rw [currentEq,entryEq] at sizeEq lenEq
  rw [currentEq] at mutable
  have layout : sourceEntry.allocation.len = sourceEntry.allocation.byteSize.bytes.toNat := by
    rw [sizeEq,lenEq,reference.size]
    exact reference.bytes
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have fits : sourceEntry.allocation.len+64 < 18446744073709551616 := by
    rw [lenEq]
    exact input.contract.resources.storageRoom (reference.id,reference.entry) member
  have referenceTracker : other.tracker = reference.tracker := Option.some.inj (other.enabled.symm.trans reference.enabled)
  rw [trackerEq,referenceTracker] at counter
  exact ⟨sizeEq,lenEq,layout,mutable,fits,counter⟩

end
end DuplicatePrefix.S02SameDestinationAcceptedEntryPhysical

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationAcceptedEntryPhysical.at_actual_call) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate site bounds dependency {dependency}"
