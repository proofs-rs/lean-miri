import duplicate_prefix.S02WildcardSameDestinationInit
import duplicate_prefix.S02WildcardPositiveIdUnique
import duplicate_prefix.S02SameDestinationUninitInitializedProtection
import duplicate_prefix.S02SameDestinationUninitInitializedBits
namespace DuplicatePrefix.S02WildcardSameDestinationAcceptedPhysical
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- The real wildcard argument and same-allocation concrete return uninit preserve
its disjoint initialized source. Physical metadata is derived from the unchanged
call contract; no successful mutation is a caller premise. -/
theorem enters
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag) :
    ∃ reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len,
      reference.id = input.contract.destination.id →
      ∃ (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
        Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
          RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
          #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),.Copy (EmptyRootArguments.second count)]
          false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
        ∃ updated : Allocation Provenance BorrowTree,
          machine.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,{reference.entry with allocation := updated}) ∧
          updated.byteSize = reference.entry.allocation.byteSize ∧ updated.len = reference.entry.allocation.len ∧
          updated.mutability = .Mut ∧ InitMaskCopy.WellFormed updated.initializationMask ∧
          updated.initializationMask.len = reference.entry.allocation.initializationMask.len ∧
          InitMaskCopy.InitializedOn updated.initializationMask (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+len)) ∧
          ProvenanceMap.clear (allocRange (Size.ofBytes input.contract.destination.offset) (Size.ofBytes 1))
            (AllocationCopy.snapshot reference.entry.allocation) (Size.ofBytes 8) reference.entry.allocation.provenanceMap =
            .ok () updated.provenanceMap := by
  obtain ⟨reference,output,fresh,run,argument,ready⟩ :=
    S02WildcardSameDestinationInitAfterArgument.ready address len count input nonempty returnTag returnConcrete
  refine ⟨reference,?_⟩
  intro same
  obtain ⟨data⟩ := ready same
  let destination := data.destination
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker fresh reference.id reference.entry output.child.tree
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let args := (RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
    reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {args with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  have frameBorrow : changed.extra.borrowTracker = some owned := by
    simp only [changed,args,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,RootFrameData.cache,
      RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,owned]
  have model := S02WildcardSeparateDestinationReady.model_after_argument input reference output fresh
  have extras : current.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) =
      some (destination.id,⟨none,#[]⟩) := by
    change (RawRootInvocation.machine #[] before).user.payload.payload.user.runtime.extras.allocations.find? _ = _
    rw [(RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2,data.sameId,same]
    exact input.return_extras
  obtain ⟨updated,protect,maskEq,clearEq,extra,bytes,length,mutable,maskWf,maskLen,_⟩ :=
    S02SameDestinationUninitInitializedProtection.invoke_concrete (options := options) (remaining := remaining+1) (span := span)
      limits.retag current model place destination data.runtime data.distinct data.order data.headroom data.nextFresh
      returnTag data.concrete #[] changed owned frameBorrow #[] extras (by simp)
  let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra destination.tracker returnTag destination.offset 1
  let after := S04ProtectUninit.finished current place destination #[] changed owned data.nextFresh tree updated
  let installed := CallEntryFacts.doneRootFrame
    {TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag with location := .unwinding ⟨559⟩}
  have actual := S02WildcardFinishFromProtect.init address len count input nonempty reference output fresh argument
    destination data.nextFresh tree updated protect
  have destEntry : destination.entry = {reference.entry with allocation := reference.entry.allocation.setExtra output.child.tree} := by
    have live := destination.live
    rw [data.sameId] at live
    exact congrArg Prod.snd (Option.some.inj (live.symm.trans (MemoryCopyBridge.live_lookup_replaced _ _ _)))
  have sourceBounds := reference.storage.bounds
  have fullFits : reference.offset.toNat+len.toNat < 2^64 := by have := reference.capacity.toNat_lt;omega
  have fullNat : (reference.offset+len).toNat = reference.offset.toNat+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt fullFits]
  have destBounds := destination.bounds
  have endFits : destination.offset.toNat+1 < 2^64 := by have := destination.capacity.toNat_lt;omega
  have endNat : (destination.offset+1).toNat = destination.offset.toNat+1 := by rw [UInt64.toNat_add];exact Nat.mod_eq_of_lt endFits
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes destination.offset) 1 (by simpa [Size.ofBytes] using endFits)
  have sourceCapacity : reference.capacity = destination.capacity := by
    have sz := destination.size
    rw [destEntry] at sz
    exact UInt64.toNat_inj.mp (congrArg (fun z : Size => z.bytes.toNat) (reference.size.symm.trans sz))
  obtain ⟨mask,maskOk,_,_,initialized⟩ := S02SameDestinationUninitInitializedBits.one_byte_frame
    reference.entry.allocation.initializationMask (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+len))
    (allocRange (Size.ofBytes destination.offset) (Size.ofBytes 1)) (Size.ofBytes (destination.offset+1))
    reference.storage.maskValid reference.storage.initialized
    (by simpa [Size.ofBytes,fullNat] using (show reference.offset.toNat < reference.offset.toNat+len.toNat by have := reference.storage.positive;omega))
    (by simpa [reference.storage.maskLength,Size.ofBytes,fullNat] using sourceBounds) endpoint
    (by simpa [Size.ofBytes,allocRange] using endNat)
    (by simpa [reference.storage.maskLength,Size.ofBytes,endNat,sourceCapacity] using destBounds)
    (by simpa [Size.ofBytes,allocRange,endNat] using data.disjoint.symm)
  have initialMaskEq : destination.entry.allocation.initializationMask = reference.entry.allocation.initializationMask := by rw [destEntry];rfl
  rw [initialMaskEq,maskOk] at maskEq
  have actualMask : mask = updated.initializationMask := Except.ok.inj maskEq
  have live : after.machine.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,{reference.entry with allocation := updated}) := by
    let protectedState := ReturnProtection.borrowedState #[] changed owned current destination.tracker data.nextFresh destination.id destination.entry tree
    change ((protectedState.machine.memory.live.filter fun row => row.1 != destination.id).push
      (destination.id,{destination.entry with allocation := updated})).find? _ = _
    rw [data.sameId]
    have entryUpdate : {destination.entry with allocation := updated} = {reference.entry with allocation := updated} := by rw [destEntry]
    rw [entryUpdate]
    exact MemoryCopyBridge.live_lookup_replaced protectedState.machine.memory reference.id _
  refine ⟨installed,after.machine,actual,updated,live,?_,?_,mutable,maskWf,?_,?_,?_⟩
  · simpa only [destEntry,Allocation.setExtra,Allocation.mapExtra,Allocation.byteSize] using bytes
  · simpa only [destEntry,Allocation.setExtra,Allocation.mapExtra,Allocation.len] using length
  · exact maskLen.trans (congrArg InitMask.len initialMaskEq)
  · rw [←actualMask];exact initialized
  · have destOffset : destination.offset = input.contract.destination.offset := data.offset
    rw [destOffset,destEntry] at clearEq
    have preserved := AllocationCopy.set_extra_preserves_storage reference.entry.allocation output.child.tree
    simpa only [preserved.2.2.2.1,preserved.2.2.2.2.2.2] using clearEq
/-- Align physical facts with any already-derived actual init witness, so the
accepted body consumes the same machine as the source/return borrow packet. -/
theorem at_actual_call
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag)
    (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len)
    (same : reference.id = input.contract.destination.id)
    (installed : CompilerFrameContext.ActualFrame) (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (actual : Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
        (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),.Copy (EmptyRootArguments.second count)]
      false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed post))
    (live : post.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry)) :
    sourceEntry.allocation.byteSize = reference.entry.allocation.byteSize ∧ sourceEntry.allocation.len = reference.entry.allocation.len ∧
    sourceEntry.allocation.len = sourceEntry.allocation.byteSize.bytes.toNat ∧ sourceEntry.allocation.mutability = .Mut ∧
    sourceEntry.allocation.len+64 < 18446744073709551616 ∧ InitMaskCopy.WellFormed sourceEntry.allocation.initializationMask ∧
    sourceEntry.allocation.initializationMask.len = reference.entry.allocation.initializationMask.len ∧
    InitMaskCopy.InitializedOn sourceEntry.allocation.initializationMask (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+len)) ∧
    ProvenanceMap.clear (allocRange (Size.ofBytes input.contract.destination.offset) (Size.ofBytes 1))
      (AllocationCopy.snapshot reference.entry.allocation) (Size.ofBytes 8) reference.entry.allocation.provenanceMap =
      .ok () sourceEntry.allocation.provenanceMap := by
  obtain ⟨other,ready⟩ := enters address len count input nonempty returnTag returnConcrete
  have idEq := S02WildcardPositiveIdUnique.same_id address len other reference
  obtain ⟨frame,machine,otherActual,updated,otherLive,bytes,length,mutable,maskWf,maskLen,initialized,clearEq⟩ := ready (idEq.trans same)
  have stateEq := (EStateM.Result.ok.inj (otherActual.symm.trans actual)).2
  have postEq : machine = post := congrArg (fun s : RootState => s.machine) stateEq
  have entryEq : other.entry = reference.entry := by
    have old := other.live
    rw [idEq] at old
    exact congrArg Prod.snd (Option.some.inj (old.symm.trans reference.live))
  have currentEq : {other.entry with allocation := updated} = sourceEntry := by
    rw [postEq,idEq] at otherLive
    exact congrArg Prod.snd (Option.some.inj (otherLive.symm.trans live))
  have allocEq : updated = sourceEntry.allocation := congrArg LocalAllocation.allocation currentEq
  have baseEq : other.base = reference.base := by
    have old := other.cachedBase
    rw [idEq] at old
    exact congrArg AllocAddresses.BaseAddressEntry.address (Option.some.inj (old.symm.trans reference.cachedBase))
  have offsetEq : other.offset = reference.offset := by
    have addressEq := other.pointerAddress.symm.trans reference.pointerAddress
    rw [baseEq] at addressEq
    exact (UInt64.add_right_inj reference.base).mp addressEq
  rw [allocEq,entryEq] at bytes length maskLen clearEq
  rw [allocEq,offsetEq] at initialized
  have storage : sourceEntry.allocation.len = sourceEntry.allocation.byteSize.bytes.toNat := by rw [bytes,length,reference.size];exact reference.bytes
  have fits : sourceEntry.allocation.len+64 < 18446744073709551616 := by
    rw [length]
    exact input.contract.resources.storageRoom (reference.id,reference.entry)
      (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live))
  exact ⟨bytes,length,storage,allocEq ▸ mutable,fits,allocEq ▸ maskWf,maskLen,initialized,clearEq⟩
end
end DuplicatePrefix.S02WildcardSameDestinationAcceptedPhysical
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02WildcardSameDestinationAcceptedPhysical.enters,``DuplicatePrefix.S02WildcardSameDestinationAcceptedPhysical.at_actual_call] do
    for dependency in (← collectAxioms name) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved wildcard same accepted physical dependency {dependency}"
