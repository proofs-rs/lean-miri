import duplicate_prefix.S02SameDestinationUninitInitializedLiteral
import duplicate_prefix.S02SameDestinationLiveTransport
import duplicate_prefix.S02SameDestinationUninitInitializedBits
import duplicate_prefix.S02ConcreteCallPreamble
import duplicate_prefix.S02PositiveFinishFrame
import duplicate_prefix.RootEntryFinish

namespace DuplicatePrefix.S02SameDestinationUninitInitializedInstalled
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section

/-- The actual call entry produces a frame and machine whose concrete return
place has the physical pointer-bounds packet required by Return. -/
theorem enters
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (frame : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
      ∃ updated : Allocation Provenance BorrowTree,
        machine.memory.live.find? (fun row => row.1 == reference.id) =
          some (reference.id,{reference.entry with allocation := updated}) ∧
        InitMaskCopy.WellFormed updated.initializationMask ∧
        updated.initializationMask.len = reference.entry.allocation.initializationMask.len ∧
        InitMaskCopy.InitializedOn updated.initializationMask
          (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+len)) ∧
        ProvenanceMap.clear (allocRange (Size.ofBytes input.contract.destination.offset) (Size.ofBytes 1))
          (AllocationCopy.snapshot reference.entry.allocation) (Size.ofBytes 8)
          reference.entry.allocation.provenanceMap = .ok () updated.provenanceMap := by
  obtain ⟨reference,firstFresh,argument,destination,secondFresh,updated,child,
      protect,destId,destEntry,destOffset,maskEq,clearEq,extra,bytes,length,mutable,
      maskWf,maskLen,pointers,afterRuntime,afterOrder,lookup,positive,active⟩ :=
    S02SameDestinationUninitInitializedLiteral.concrete_after_argument_literal id tag address len count input nonempty sameAllocation
      returnTag returnConcrete
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker firstFresh
    reference.id reference.entry tag reference.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
    destination.tracker returnTag destination.offset 1
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  let done := Storage.withCurrent #[] installed after.machine
  have shape := S02PositiveFinishFrame.after_destination_registration root
    (RawRootInvocation.locals before place input.contract.model.noDataRace)
    adjusted count reference.id destination.id reference.tracker.global.nextPointerTag
    destination.tracker.global.nextPointerTag
  obtain ⟨body,size,dead,noClocks⟩ := shape
  have finish := RootEntryFinish.actual_finish options limits (remaining+1) span #[] protectedFrame after.machine
    body size (dead ⟨0,by decide⟩ (by omega) (Or.inl rfl))
    (dead ⟨6,by decide⟩ (by omega) (Or.inr (Or.inl rfl)))
    (dead ⟨13,by decide⟩ (by omega) (Or.inr (Or.inr (Or.inl rfl))))
    (dead ⟨14,by decide⟩ (by omega) (Or.inr (Or.inr (Or.inr rfl)))) noClocks
  let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
  have localSpan := CallEntryLocals.root_span0 options limits (remaining+1) span #[] frame current
    (by rfl) (by rfl) (by rfl)
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] frame current
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] frame changed current
  have compat : h.checkArgumentCompat () RootCompilerFacts.rootAbi.ret RootCompilerFacts.rootAbi.ret
      (Storage.withCurrent #[] changed current) = .ok true (Storage.withCurrent #[] changed current) := by
    change (config options (remaining+1) span).calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [(actual_fields options () (remaining+1) span).callCompiler]
    exact CallEntryFacts.root_return_argument_compat _ options.compatibilityBudget _
  have tail : RootEntryTail.tail h place (Storage.withCurrent #[] frame current) = .ok () done := by
    unfold RootEntryTail.tail RootCallCore.spanAt
    simp only [bind,EStateM.bind]
    rw [localSpan]
    simp only [EStateM.bind]
    rw [getFrame]
    simp only [EStateM.bind]
    dsimp only [changed] at setFrame
    rw [setFrame]
    simp only [EStateM.bind]
    dsimp only [changed] at compat
    rw [compat]
    simp only [EStateM.bind,Bool.not_true,ite_false,pure,EStateM.pure]
    change (do
      TypedRetag.protectInPlaceFunctionArgument
        (config options (remaining+1) span).retag limits.retag place
      RootEntryFinish.finish h) (Storage.withCurrent #[] changed current) = .ok () done
    simp only [bind,EStateM.bind]
    rw [protect]
    simp only [EStateM.bind]
    change RootEntryFinish.finish
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      (Storage.withCurrent #[] protectedFrame after.machine) = .ok () done
    exact finish
  obtain ⟨preambleAfter,preambleArg,preambleContinue⟩ :=
    S02ConcreteCallPreamble.prefix_and_continuation id tag address len count input nonempty
  have sameAfter : preambleAfter = Storage.withCurrent #[] frame current := by
    have resultEq := preambleArg.symm.trans argument
    exact (EStateM.Result.ok.inj resultEq).2
  have actualCall := preambleContinue done (sameAfter ▸ tail)
  have refId : id = reference.id := by
    have h := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at h
    exact h.1
  have sameId : destination.id = reference.id := destId.trans (sameAllocation.symm.trans refId)
  have sourceBounds := reference.storage.bounds
  have fullFits : reference.offset.toNat+len.toNat < 2^64 := by
    have := reference.capacity.toNat_lt
    omega
  have fullNat : (reference.offset+len).toNat = reference.offset.toNat+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt fullFits]
  have destBounds := destination.bounds
  have endFits : destination.offset.toNat+1 < 2^64 := by
    have := destination.capacity.toNat_lt
    omega
  have endNat : (destination.offset+1).toNat = destination.offset.toNat+1 := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt endFits
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes destination.offset) 1
    (by simpa [Size.ofBytes] using endFits)
  have sourceCapacity : reference.capacity = destination.capacity := by
    have sz := destination.size
    rw [destEntry] at sz
    exact UInt64.toNat_inj.mp (by
      have eq := congrArg (fun z : Size => z.bytes.toNat) (reference.size.symm.trans sz)
      exact eq)
  have separate := S02SameDestinationLiveTransport.actual_reference_disjoint
    id tag address len input nonempty sameAllocation reference
  rw [←destOffset] at separate
  obtain ⟨mask,maskOk,_,_,initialized⟩ := S02SameDestinationUninitInitializedBits.one_byte_frame
    reference.entry.allocation.initializationMask
    (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+len))
    (allocRange (Size.ofBytes destination.offset) (Size.ofBytes 1))
    (Size.ofBytes (destination.offset+1)) reference.storage.maskValid reference.storage.initialized
    (by simpa [Size.ofBytes,fullNat] using (show reference.offset.toNat < reference.offset.toNat+len.toNat by have := reference.storage.positive; omega))
    (by simpa [reference.storage.maskLength,Size.ofBytes,fullNat] using sourceBounds)
    endpoint (by simpa [Size.ofBytes,allocRange] using endNat)
    (by simpa [reference.storage.maskLength,Size.ofBytes,endNat,sourceCapacity] using destBounds)
    (by simpa [Size.ofBytes,allocRange,fullNat,endNat] using separate)
  have initialMaskEq : destination.entry.allocation.initializationMask = reference.entry.allocation.initializationMask := by
    rw [destEntry]
    rfl
  rw [initialMaskEq,maskOk] at maskEq
  have actualMask : mask = updated.initializationMask := Except.ok.inj maskEq
  have live : after.machine.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,{reference.entry with allocation := updated}) := by
    let protectedState := ReturnProtection.borrowedState #[] changed owned current destination.tracker secondFresh destination.id destination.entry tree
    change ((protectedState.machine.memory.live.filter fun row => row.1 != destination.id).push
      (destination.id,{destination.entry with allocation := updated})).find? _ = _
    rw [sameId]
    have entryUpdate : {destination.entry with allocation := updated} =
        {reference.entry with allocation := updated} := by rw [destEntry]
    rw [entryUpdate]
    exact MemoryCopyBridge.live_lookup_replaced protectedState.machine.memory reference.id _
  rw [destOffset,destEntry] at clearEq
  refine ⟨reference,installed,after.machine,actualCall,updated,live,maskWf,?_,?_,?_⟩
  · exact maskLen.trans (congrArg InitMask.len initialMaskEq)
  · rw [←actualMask]
    exact initialized
  · exact clearEq

end
end DuplicatePrefix.S02SameDestinationUninitInitializedInstalled
