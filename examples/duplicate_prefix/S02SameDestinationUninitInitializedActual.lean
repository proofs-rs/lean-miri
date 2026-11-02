import duplicate_prefix.S02SameDestinationUninitInitializedInstalled


namespace DuplicatePrefix.S02SameDestinationUninitInitializedActual
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
    InitMaskCopy.WellFormed sourceEntry.allocation.initializationMask ∧
    sourceEntry.allocation.initializationMask.len = reference.entry.allocation.initializationMask.len ∧
    InitMaskCopy.InitializedOn sourceEntry.allocation.initializationMask
      (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+len)) ∧
    ProvenanceMap.clear (allocRange (Size.ofBytes input.contract.destination.offset) (Size.ofBytes 1))
      (AllocationCopy.snapshot reference.entry.allocation) (Size.ofBytes 8)
      reference.entry.allocation.provenanceMap = .ok () sourceEntry.allocation.provenanceMap := by
  obtain ⟨other,otherFrame,otherPost,otherActual,updated,otherLive,maskWf,maskLen,initialized,clearEq⟩ :=
    S02SameDestinationUninitInitializedInstalled.enters id tag address len count input nonempty
      sameAllocation returnTag returnConcrete
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
  have currentEq : {other.entry with allocation := updated} = sourceEntry := by
    have h := otherLive
    rw [postEq,idEq] at h
    exact congrArg Prod.snd (Option.some.inj (h.symm.trans live))
  have allocEq : updated = sourceEntry.allocation := congrArg LocalAllocation.allocation currentEq
  have baseEq : other.base = reference.base := by
    have cached := other.cachedBase
    rw [idEq] at cached
    exact congrArg AllocAddresses.BaseAddressEntry.address (Option.some.inj (cached.symm.trans reference.cachedBase))
  have offsetEq : other.offset = reference.offset := by
    have pointer := other.pointerAddress.symm.trans reference.pointerAddress
    rw [baseEq] at pointer
    exact (UInt64.add_right_inj reference.base).mp pointer
  rw [allocEq,entryEq] at maskLen clearEq
  rw [allocEq,offsetEq] at initialized
  exact ⟨allocEq ▸ maskWf,maskLen,initialized,clearEq⟩

end
end DuplicatePrefix.S02SameDestinationUninitInitializedActual
