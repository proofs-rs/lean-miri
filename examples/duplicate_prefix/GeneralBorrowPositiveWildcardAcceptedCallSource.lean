import duplicate_prefix.GeneralBorrowPositiveWildcardAcceptedToCopy
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardAcceptedCallSource
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open GeneralBorrowExposedScopedAcceptedExpression
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
set_option autoImplicit false in
structure Facts (s : GeneralBorrowPositiveWildcardAcceptedInput.Initial) (updated : Allocation Provenance BorrowTree)
    (call : GeneralBorrowExposedScopedAsMutToCopy.Input) : Prop where
  options : call.options=s.options
  limits : call.limits=s.limits
  remaining : call.remaining=s.remaining
  span : call.span=s.span
  id : call.id=s.id
  base : call.base=s.base
  offset : call.offset=0
  len : call.len=s.len
  parentTag : call.parentTag=GeneralBorrowPositiveWildcardAcceptedInput.mutableTag s.toInitial
  tracker : call.tracker=ReferenceBorrowDriver.allocatedTracker (GeneralBorrowPositiveWildcardAcceptedInput.lenEnded s.toInitial) s.mutableFresh
  bufferSize : call.entry.allocation.byteSize=s.entry.allocation.byteSize
  bufferLen : call.entry.allocation.len=s.entry.allocation.len
  bufferMask : call.entry.allocation.initializationMask=s.entry.allocation.initializationMask
  bufferProvenance : call.entry.allocation.provenanceMap=s.entry.allocation.provenanceMap
  bufferMutable : call.entry.allocation.mutability=s.entry.allocation.mutability
  bufferBytes : AllocationCopy.snapshot call.entry.allocation=AllocationCopy.snapshot s.entry.allocation
  storage : call.entry.allocation.len=call.entry.allocation.byteSize.bytes.toNat
  maskValid : InitMaskCopy.WellFormed call.entry.allocation.initializationMask
  maskLength : call.entry.allocation.initializationMask.len=call.entry.allocation.byteSize
  initialized : InitMaskCopy.InitializedOn call.entry.allocation.initializationMask (Size.ofBytes call.offset) (Size.ofBytes (call.offset+s.count))
  provenance : ProvenanceCopy.WellFormed call.entry.allocation.provenanceMap call.entry.allocation.len
  storageFits : call.entry.allocation.len+64<18446744073709551616
  mutable : call.entry.allocation.mutability=.Mut
  runtime : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before call.machine
  bufferExtras : call.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==call.id)=some (call.id,⟨none,#[]⟩)
  slotExtras : call.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==s.slotId)=some (s.slotId,⟨none,#[]⟩)
  slotCached : call.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==s.slotId)=some ⟨s.slotId,s.slotBase⟩
  slotPresent : call.machine.memory.live.find? (fun row=>row.1==s.slotId)=some (s.slotId,{s.slotEntry with allocation:=updated})
  slotTree : updated.extra=PhysicalMachineWrite.slotTree s.slotRoot (GeneralBorrowPositiveWildcardFunctionState.next s.tracker s.fresh).global.nextPointerTag 1 true
  slotSize : updated.byteSize=Size.ofBytes 1
  slotLen : updated.len=1
  slotMask : updated.initializationMask=InitMask.new (Size.ofBytes 1) false
  slotProvenance : updated.provenanceMap=ProvenanceMap.new
  slotBytes : AllocationCopy.snapshot updated=AllocationCopy.snapshot s.slotEntry.allocation
  slotMutable : updated.mutability=.Mut
  continuation : call.caller.returnContinuation=.stop true
  returnPlace : call.caller.returnPlace.toRuntimePlace=⟨.memory s.place.mplace,s.place.layout⟩
  varargs : call.caller.vaList=#[]
  frameBorrow : call.caller.extra.borrowTracker=some ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).addProtector s.slotId
    (GeneralBorrowPositiveWildcardFunctionState.next s.tracker s.fresh).global.nextPointerTag)
  local0 : call.caller.locals[0]?=some ⟨.live (.immediate .uninit),none⟩
  sourceSlot2 : call.caller.locals[2]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 s.count)))),some RootCompilerFacts.usizeLayout⟩
  accessEq : (ActualReferenceContext.config call.options call.remaining call.span).access=s.validationContext.access
  outerAccessEq : (ActualReferenceContext.config call.options (call.remaining+1) call.span).access=s.writeContext.access

theorem build (s : GeneralBorrowPositiveWildcardAcceptedInput.Initial) (updated : Allocation Provenance BorrowTree)
    (i : GeneralBorrowExposedScopedLenCallInput.Input) (stage : GeneralBorrowExposedScopedAcceptedAfterLen.Initial)
    (expression : GeneralBorrowExposedScopedAcceptedExpression.Input) (call : GeneralBorrowExposedScopedAsMutToCopy.Input)
    (origin : GeneralBorrowPositiveWildcardAcceptedAfterLen.Origin s updated i stage)
    (expressionOrigin : GeneralBorrowExposedScopedAcceptedAfterLen.Origin stage expression)
    (callOrigin : GeneralBorrowExposedScopedAcceptedToAsMut.Origin expression call.toInput) : Facts s updated call := by
  have options:=callOrigin.options.trans (expressionOrigin.options.trans origin.options)
  have limits:=callOrigin.limits.trans (expressionOrigin.limits.trans origin.limits)
  have remaining:=callOrigin.remaining.trans (expressionOrigin.remaining.trans origin.remaining)
  have span:=callOrigin.span.trans (expressionOrigin.span.trans origin.span)
  have id:=callOrigin.id.trans (expressionOrigin.id.trans origin.id)
  have base:=callOrigin.base.trans (expressionOrigin.base.trans origin.base)
  have offset:=callOrigin.offset.trans (expressionOrigin.offset.trans origin.offset)
  have len:=callOrigin.len.trans (expressionOrigin.len.trans origin.len)
  have sourceTracker : expression.tracker=GeneralBorrowPositiveWildcardAcceptedInput.lenEnded s.toInitial :=
    expressionOrigin.tracker.trans (origin.tracker.trans (GeneralBorrowPositiveWildcardAcceptedDefaultData.tracker_eq s updated i origin.lenOrigin))
  have parentTag : call.parentTag=GeneralBorrowPositiveWildcardAcceptedInput.mutableTag s.toInitial := by
    rw [callOrigin.parentTag,sourceTracker]
  have tracker : call.tracker=ReferenceBorrowDriver.allocatedTracker (GeneralBorrowPositiveWildcardAcceptedInput.lenEnded s.toInitial) s.mutableFresh := by
    have eq:=callOrigin.tracker
    simpa only [expressionTracker,sourceTracker] using eq
  have bufferSize : call.entry.allocation.byteSize=s.entry.allocation.byteSize := by
    rw [callOrigin.entry]
    change expression.entry.allocation.byteSize=_
    rw [expressionOrigin.entry,origin.entry]
    exact origin.lenOrigin.bufferSize
  have bufferLen : call.entry.allocation.len=s.entry.allocation.len := by
    rw [callOrigin.entry]
    change expression.entry.allocation.len=_
    rw [expressionOrigin.entry,origin.entry]
    exact origin.lenOrigin.bufferLen
  have bufferMask : call.entry.allocation.initializationMask=s.entry.allocation.initializationMask := by
    rw [callOrigin.entry]
    change expression.entry.allocation.initializationMask=_
    rw [expressionOrigin.entry,origin.entry]
    exact origin.lenOrigin.bufferMask
  have bufferProvenance : call.entry.allocation.provenanceMap=s.entry.allocation.provenanceMap := by
    rw [callOrigin.entry]
    change expression.entry.allocation.provenanceMap=_
    rw [expressionOrigin.entry,origin.entry]
    exact origin.lenOrigin.bufferProvenance
  have bufferMutable : call.entry.allocation.mutability=s.entry.allocation.mutability := by
    rw [callOrigin.entry]
    change expression.entry.allocation.mutability=_
    rw [expressionOrigin.entry,origin.entry]
    exact origin.lenOrigin.bufferMutable
  have bufferBytes : AllocationCopy.snapshot call.entry.allocation=AllocationCopy.snapshot s.entry.allocation := by
    rw [callOrigin.entry]
    change AllocationCopy.snapshot expression.entry.allocation=_
    rw [expressionOrigin.entry,origin.entry]
    exact origin.lenOrigin.bufferBytes
  have mf:=GeneralBorrowExposedScopedAcceptedAfterLen.machine_facts stage
  have addresses : call.machine.user.addresses=s.before.user.addresses := by
    rw [callOrigin.machine]
    change expression.machine.user.addresses=_
    rw [expressionOrigin.machine,mf.addresses]
    exact origin.runtime.addresses
  have types : call.machine.user.payload.payload.user.types=s.before.user.payload.payload.user.types := by
    rw [callOrigin.machine]
    change expression.machine.user.payload.payload.user.types=_
    rw [expressionOrigin.machine,mf.types]
    exact origin.runtime.types
  have extras : call.machine.user.payload.payload.user.runtime.extras=s.before.user.payload.payload.user.runtime.extras := by
    rw [callOrigin.machine]
    change expression.machine.user.payload.payload.user.runtime.extras=_
    rw [expressionOrigin.machine,mf.extras]
    exact origin.runtime.extras
  have runtime : GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before call.machine := by
    exact ⟨call.ghost,call.shallow,call.race,addresses,types,extras,call.backend,
      (by simpa only [options,remaining,span] using call.unchecked),(by simpa only [options,remaining,span] using call.noGc),
      call.fixed,⟨call.thread,call.active,call.top⟩⟩
  have slotPresent : call.machine.memory.live.find? (fun row=>row.1==s.slotId)=some (s.slotId,{s.slotEntry with allocation:=updated}) := by
    rw [callOrigin.machine]
    apply StackPopRelease.lookup_commit_other expression.machine.memory expression.id s.slotId expression.entry _ (expressionTree expression)
    · rw [expressionOrigin.id,origin.id]
      exact s.separate
    · rw [expressionOrigin.machine,mf.memory]
      exact origin.slotPresent
  have keep (index : Nat) (different : index≠16) : call.caller.locals[index]?=expression.caller.locals[index]? := by
    rw [callOrigin.caller]
    simp [expressionFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem?_set,Ne.symm different]
  have continuation : call.caller.returnContinuation=.stop true := by
    rw [callOrigin.caller]
    change expression.caller.returnContinuation=_
    rw [expressionOrigin.frame.continuation]
    exact origin.continuation
  have returnPlace : call.caller.returnPlace.toRuntimePlace=⟨.memory s.place.mplace,s.place.layout⟩ := by
    rw [callOrigin.caller]
    change expression.caller.returnPlace.toRuntimePlace=_
    rw [expressionOrigin.frame.returnPlace]
    exact origin.returnPlace
  have varargs : call.caller.vaList=#[] := by
    rw [callOrigin.caller]
    change expression.caller.vaList=_
    rw [expressionOrigin.frame.varargs]
    exact origin.varargs
  have frameBorrow : call.caller.extra.borrowTracker=some ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).addProtector s.slotId
      (GeneralBorrowPositiveWildcardFunctionState.next s.tracker s.fresh).global.nextPointerTag) := by
    rw [callOrigin.caller]
    change expression.caller.extra.borrowTracker=_
    rw [expressionOrigin.frame.extra]
    exact origin.frameBorrow
  refine ⟨options,limits,remaining,span,id,base,offset,len,parentTag,tracker,bufferSize,bufferLen,bufferMask,bufferProvenance,bufferMutable,bufferBytes,
    ?_,?_,?_,?_,?_,?_,bufferMutable.trans s.bufferMutable,runtime,?_,?_,?_,slotPresent,
    origin.lenOrigin.slotTree,origin.lenOrigin.slotSize,origin.lenOrigin.slotLen,origin.lenOrigin.slotMask,origin.lenOrigin.slotProvenance,origin.lenOrigin.slotBytes,origin.lenOrigin.slotMutable,
    continuation,returnPlace,varargs,frameBorrow,?_,?_,?_,?_⟩
  · rw [bufferLen,bufferSize];exact s.bufferStorage
  · rw [bufferMask];exact s.bufferMaskValid
  · rw [bufferMask,bufferSize];exact s.bufferMaskLength
  · rw [bufferMask,offset,UInt64.zero_add];exact s.bufferInitialized
  · rw [bufferProvenance,bufferLen];exact s.bufferProvenance
  · rw [bufferLen];exact s.bufferStorageFits
  · rw [extras,id];exact s.bufferExtras
  · rw [extras];exact s.extras
  · rw [addresses];exact s.slotCached
  · rw [keep 0 (by decide),expressionOrigin.kept.slot0]
    exact stage.frameFacts.slot0
  · rw [keep 2 (by decide),expressionOrigin.frame.slot2]
    exact origin.sourceSlot2
  · rw [options,remaining,span];exact s.accessEq
  · rw [options,remaining,span];exact s.outerAccessEq
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardAcceptedCallSource
