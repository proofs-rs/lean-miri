import duplicate_prefix.S02SameDestinationAcceptedGuardControl
import duplicate_prefix.S02SameDestinationAcceptedEntryPhysical
import duplicate_prefix.S02SameDestinationUninitInitializedActual
import duplicate_prefix.S02SameDestinationUninitProvenanceResult
import duplicate_prefix.S02SameDestinationAcceptedCopyDestination
import duplicate_prefix.S02SameDestinationAcceptedResultJoin
import duplicate_prefix.S02SameDestinationRejectedResultLiteralActivity
import duplicate_prefix.S02SameDestinationRejectedResultOrder
import duplicate_prefix.S02SameDestinationRejectedResultLookup
import duplicate_prefix.S02SameDestinationInstalledReturnFrame
import duplicate_prefix.S02DisjointSharedLenLiteral
import duplicate_prefix.S02HiddenLeafActiveRelease
import duplicate_prefix.S03ActiveSameReturnStepBounds
import duplicate_prefix.CanonicalCopyBound

namespace DuplicatePrefix.S02SameDestinationAcceptedResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The original positive concrete same-allocation call executes the actual
accepted copy and Return(true), with successful progress on every reachable
finite prefix. All current copy and return facts come from the call contract. -/
theorem result
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
    (countPositive : (0 : UInt64) < count) (within : count ≤ len/2) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len count place := by
  obtain ⟨reference,tracker,sourceEntry,rawShared,entry,frame,guard,initial,post,guardTree,held,sharedChild,facts,
    original,packetTracker,sourceSame,sourceOffset,sourceLen,nodeMargin,tagMargin,raw,
    rawTag,rawParent,rawSelected,rawMaximum,rawOffset,rawLen,_initialOrder,
    guardBody,guardIdentity,guardCallee,track,relevant,noClocks,defaultMode,cachedAddress,
    metadata,notConstructed,currentLive,sourceExtras,capacity,headroom,tagsRoom,positive,nonzero,
    signed,bounds,dynamicPositive,validationPositive,dispatchPositive,valid1,valid15,valid16,
    sourceLive,sourceCached,dest15Live,dest15Uncached,dest16Live,dest16Uncached,guardOrder⟩ :=
    S02SameDestinationAcceptedGuardControl.ready_control id tag address len count input nonempty
      sameAllocation returnTag returnConcrete countPositive within
  obtain ⟨actual,prefixTrace,guardTrace,location,slot0,slot1,slot2,slot13,slot15,slot16,high,shape,
    body,bodyEntry,identity,identityEntry,callee,calleeEntry,extra,extraEntry,placeEq,placeEntry,
    contEq,contEntry,vaEq,vaEntry,localId,localIdEntry,resultTrack,size,all,postMemory,postTracker,mode,runtime,
    readPositive,bothPositive,sourceActivity,graph,sharedTag,live,tracked,addresses,types,extras,ghost,
    shallow,race,backend,unchecked,noGc,fixed,thread,active,topZero,fresh,literal,sharedOffset,sharedLen⟩ := facts
  obtain ⟨sourceId,sourceTag,sourceEntryEq,sourceChild,oldNode,oldPresent,oldTag,oldHidden,oldTagged⟩ :=
    S02SameDestinationRejectedSourceNode.preserved id tag address len count input nonempty
      sameAllocation returnTag returnConcrete reference tracker held sourceEntry rawShared entry initial actual
      original sourceSame live sharedTag guardTree graph
  obtain ⟨sizeEq,lenEq,storage,mutable,storageFits,counter⟩ :=
    S02SameDestinationAcceptedEntryPhysical.at_actual_call id tag address len count input nonempty
      sameAllocation returnTag returnConcrete reference tracker sourceEntry entry initial actual tracked live
  obtain ⟨maskValid,maskLength,initialized,cleared⟩ :=
    S02SameDestinationUninitInitializedActual.at_actual_call id tag address len count input nonempty
      sameAllocation returnTag returnConcrete reference tracker sourceEntry entry initial actual tracked live
  have snapshotLen : (AllocationCopy.snapshot reference.entry.allocation).size = reference.entry.allocation.len := by
    cases reference.entry.allocation
    simp [AllocationCopy.snapshot,Allocation.inspectWithUninitAndPtrOutsideInterpreter,Allocation.len,
      Pure.pure,Except.pure,Except.toOption,Option.getD]
  have initialFits : reference.entry.allocation.len < 2^64 := by rw [reference.bytes];exact reference.capacity.toNat_lt
  have returnFits : input.contract.destination.offset.toNat+1 < 2^64 := by
    have bounds := input.contract.destination.bounds
    have cap := input.contract.destination.capacity.toNat_lt
    omega
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes input.contract.destination.offset) 1
    (by simpa only [Size.ofBytes,UInt64.toNat_one] using returnFits)
  have direct := S02SameDestinationUninitProvenanceResult.after_clear
    reference.entry.allocation.provenanceMap sourceEntry.allocation.provenanceMap
    (allocRange (Size.ofBytes input.contract.destination.offset) (Size.ofBytes 1))
    (Size.ofBytes (input.contract.destination.offset+1)) (AllocationCopy.snapshot reference.entry.allocation)
    (by simpa only [snapshotLen] using reference.provenanceMap) (by change (1 : UInt64) ≠ 0;decide) endpoint
    (by simpa only [snapshotLen] using initialFits) cleared
  have currentDirect : S02SameDestinationUninitProvenanceInput.DirectInput sourceEntry.allocation.provenanceMap sourceEntry.allocation.len := by
    simpa only [snapshotLen,←lenEq] using direct
  have sourceMaskLen : sourceEntry.allocation.initializationMask.len = sourceEntry.allocation.byteSize :=
    maskLength.trans (reference.storage.maskLength.trans (reference.size.symm.trans sizeEq.symm))
  have sumFits : reference.offset.toNat+len.toNat < 2^64 := by
    have cap := sourceEntry.allocation.byteSize.bytes.toNat_lt
    omega
  have countLe : count.toNat ≤ len.toNat := by
    have h := UInt64.le_iff_toNat_le.mp within
    rw [UInt64.toNat_div] at h
    have small := Nat.div_le_self len.toNat 2
    simpa only [show (2 : UInt64).toNat = 2 from rfl] using Nat.le_trans h small
  have countEnd : (reference.offset+count).toNat ≤ (reference.offset+len).toNat := by
    simp only [UInt64.toNat_add,Nat.mod_eq_of_lt sumFits,
      Nat.mod_eq_of_lt (show reference.offset.toNat+count.toNat<2^64 by omega)]
    omega
  have sourceInitialized := S02SameDestinationAcceptedResultJoin.initialized_subrange
    sourceEntry.allocation.initializationMask (Size.ofBytes reference.offset) (Size.ofBytes (reference.offset+len))
    (Size.ofBytes (reference.offset+count)) initialized countEnd
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {sourceEntry with allocation := sourceEntry.allocation.setExtra guardTree}
  have initialActivity : GeneralBorrowFreshActiveWithin.ActiveWithin guardTree rawShared.parent .Write reference.offset (reference.offset+len) := sourceActivity
  have limitPositive : 0 < limits.validation := by
    have h := input.contract.resources.executionFuel.2.2.2
    unfold work at h;omega
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span
    input.contract.model.preciseOff input.contract.model.implicitOff
  obtain ⟨copyPacket,copied,done,finalMachine,protectedEq,counterGrowth,sourceMetadata,copyTrace,ready,
    copyMemory,copyLive,copySize,copyLen,copyRuntime,copyPositive,copyActivity,copyTracked,copyAddresses,copyExtras,
    copyBackend,copyGhost,copyShallow,copyRace,copyFixed,copyUnchecked,copyNoGc,connection,physical,copyThread⟩ :=
    S02SameDestinationAcceptedSourceLedger.invoke options limits remaining span ctx
      input.contract.model.debugOff input.contract.model.nullComparator
      (options.place.dynamicFuel-1) (options.limits.validation-1)
      (Nat.sub_add_cancel dynamicPositive).symm (Nat.sub_add_cancel validationPositive).symm
      reference.id buffer reference.base reference.offset len raw.parentTag positive nonzero signed bounds
      guard post held postTracker defaultMode raw.tagRoom runtime raw rfl rawOffset rawLen capacity
      valid15 dest15Live dest15Uncached noClocks ghost shallow cachedAddress currentLive race metadata
      notConstructed thread active headroom tagsRoom input.contract.model.preciseOff input.contract.model.implicitOff
      (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
      (limits.callDispatch-1) (Nat.sub_add_cancel dispatchPositive).symm backend unchecked noGc fixed
      topZero size guardBody guardIdentity guardCallee track relevant all location valid16 dest16Live dest16Uncached
      valid1 sourceLive sourceCached count countPositive within slot2 slot13 high rawShared.parent
      initialActivity slot0 (limits.validation-1) (Nat.sub_add_cancel limitPositive).symm
      storage maskValid sourceMaskLen sourceInitialized currentDirect storageFits mutable sourceExtras
      (CanonicalCopyBound.guarded options () (remaining+1) span len count within)
  have sharedRoom : sourceEntry.allocation.extra.nodes.size+2 < 65536 := by omega
  have sharedTagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615 := by omega
  have initialReturnPresent : sourceEntry.allocation.extra.nodeAt original.child = some original.returnNode := by
    rw [←sourceEntryEq];exact original.returnPresent
  have initialReturnActivity : GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra original.child .Write
      original.destination.offset (original.destination.offset+1) := by
    rw [←sourceEntryEq];exact original.activity
  have different : original.child ≠ rawShared.parent := by rw [←sourceChild];exact original.childrenDifferent
  have literalEq : guardTree = GeneralBorrowRawSharedToLenLiteralLedger.finalTree sourceEntry.allocation.extra tracker
      rawShared.parentTag rawShared.offset rawShared.len rawShared.tagRoom := by
    simpa only [sharedTag,sharedOffset,sharedLen] using literal
  obtain ⟨guardReturnActivity,guardReturnNode,guardReturnPresent,guardReturnSame,guardReturnEdge,
    guardReturnLeaf,guardReturnHidden⟩ :=
    S02SameDestinationRejectedResultLiteralActivity.preserves sourceEntry.allocation.extra tracker reference.id
      (by rw [←sourceEntryEq,←packetTracker];exact original.runtime) rawShared sharedRoom
      (by omega) sharedTagRoom original.child original.returnNode initialReturnPresent original.returnLeaf
      original.returnHidden different original.destination.offset (original.destination.offset+1) initialReturnActivity
  rw [←literalEq] at guardReturnActivity guardReturnPresent
  have guardReturnTagged : guardTree.indexOfTag original.returnTag = some original.child := by
    obtain ⟨node,present,tagEq,parentEq,hiddenEq,tagged⟩ := graph.oldNodes original.child original.returnNode initialReturnPresent
    rw [←original.returnSame];exact tagged
  have guardParentTagged : guardTree.indexOfTag original.destination.tag = some original.destination.parent := by
    rw [literalEq]
    exact S02SameDestinationRejectedResultLookup.literal sourceEntry.allocation.extra tracker reference.id
      (by rw [←sourceEntryEq,←packetTracker];exact original.runtime) rawShared sharedRoom
      (by omega) sharedTagRoom original.destination.tag original.destination.parent
      (by rw [←sourceEntryEq];exact original.destination.tagged)
  have initialReturnPositive : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra tracker.global.protectedTags
      (some original.child) (some original.selected) original.maximum original.destination.offset 1 := by
    rw [←sourceEntryEq,←packetTracker];exact original.positive
  have disjoint : rawShared.offset.toNat+rawShared.len.toNat ≤ original.destination.offset.toNat ∨
      (original.destination.offset+1).toNat ≤ rawShared.offset.toNat := by
    have stop : (original.sourceOffset+original.sourceLen).toNat = original.sourceOffset.toNat+original.sourceLen.toNat := by
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt]
      exact Nat.lt_of_le_of_lt original.sourcePositive.bounds original.destination.entry.allocation.extra.locations.size.bytes.toNat_lt
    simpa only [sharedOffset,sharedLen,←sourceOffset,←sourceLen,stop] using original.disjoint
  obtain ⟨guardReturnPositive⟩ := S02DisjointSharedLenLiteral.destination sourceEntry.allocation.extra tracker reference.id
    (by rw [←sourceEntryEq,←packetTracker];exact original.runtime) rawShared sharedRoom (by omega) sharedTagRoom
    (some original.child) (some original.selected) original.maximum original.destination.offset 1 disjoint initialReturnPositive
  rw [←literalEq,←graph.protections] at guardReturnPositive
  have rawOutside : raw.offset.toNat+raw.len.toNat ≤ original.destination.offset.toNat ∨      (original.destination.offset+1).toNat ≤ raw.offset.toNat := by
    simpa only [rawOffset,rawLen,sharedOffset,sharedLen] using disjoint
  obtain ⟨⟨returnPositive⟩,returnActivity,⟨returnNode,returnPresent,returnSame,returnEdge,returnLeaf,returnHidden⟩,
    currentOrder,currentTags,currentCapacity⟩ :=
    S02SameDestinationAcceptedCopyDestination.current buffer post reference.id reference.base reference.offset len count
      held runtime raw headroom tagsRoom guardOrder copyPacket copied connection
      original.child original.selected original.maximum original.destination.offset 1 rawOutside guardReturnPositive
      guardReturnNode guardReturnPresent guardReturnLeaf guardReturnHidden
      (by rw [rawParent];exact different) guardReturnActivity
  have finalParentTagged := currentTags original.destination.tag original.destination.parent guardParentTagged
  have finalAddresses : finalMachine.user.addresses = initial.user.addresses := by
    rw [copyAddresses,addresses]
    exact (S02SeparateDestinationTickLedger.preserved options remaining span initial).2.2.2.2.1
  have finalLive : finalMachine.memory.live.find? (fun row => row.1 == original.destination.id) =
      some (original.destination.id,⟨original.destination.entry.kind,copied⟩) := by
    rw [sourceId,sourceEntryEq];exact copyLive
  let destination := S02SameDestinationAcceptedResultJoin.destination original.destination copied finalLive finalAddresses
    (by rw [sourceEntryEq];exact copySize) (by rw [sourceEntryEq];exact copyLen) physical
    (by rw [sourceEntryEq];exact currentCapacity.trans graph.capacity) finalParentTagged
  have sourcePresent : guardTree.nodeAt raw.parent = some oldNode := by rw [rawParent];exact oldPresent
  obtain ⟨sourceNode,sourceNodePresent,sourceNodeTag,sourceNodeExposure⟩ := sourceMetadata.oldNode oldNode sourcePresent
  have sourceHidden : sourceNode.isExposed = false := sourceNodeExposure.trans oldHidden
  have sourceTagged : copied.extra.indexOfTag raw.parentTag = some raw.parent := by
    apply sourceMetadata.tagged oldNode sourcePresent
    exact oldTag.trans rawTag.symm
  have sourceActive : GeneralBorrowFreshActiveWithin.ActiveWithin copied.extra raw.parent .Write
      reference.offset (reference.offset+len) := by rw [rawParent];exact copyActivity
  have currentReturnTagged := currentTags original.returnTag original.child guardReturnTagged
  have currentReturnSame : returnNode.tag = original.returnTag := returnSame.trans (guardReturnSame.trans original.returnSame)
  have currentReturnEdge : returnNode.parent = some destination.parent := returnEdge.trans (guardReturnEdge.trans original.returnEdge)
  have sourceOwned : original.borrowFrame.protectedTags =
      #[(destination.id,raw.parentTag),(destination.id,original.returnTag)] := by
    change original.borrowFrame.protectedTags = _
    rw [rawTag,←sourceTag];exact original.owned
  have hiddenFrame := S02SameDestinationHiddenFrame.of_hidden copied.extra (GeneralBorrowRawAsMutToCopy.held copyPacket).global
    original.borrowFrame destination.id destination.id raw.parentTag original.returnTag original.child returnNode sourceOwned
    copyRuntime raw.parent sourceNode sourceTagged sourceNodePresent sourceHidden currentReturnTagged returnPresent returnHidden
  obtain ⟨sourcePositive⟩ := copyPositive
  have afterSourceActivity := S02HiddenLeafActiveRelease.release copied.extra (GeneralBorrowRawAsMutToCopy.held copyPacket).global
    copyRuntime raw.parentTag raw.parent copyPacket.selected copyPacket.maximum reference.offset len sourcePositive
    sourceNode sourceNodePresent sourceHidden sourceTagged sourceMetadata.distinct
    (fun _ _ => currentOrder) sourceMetadata.short sourceActive original.child returnNode returnPresent returnLeaf returnHidden
    (by rw [rawParent];exact different) destination.offset (destination.offset+1) returnActivity
  obtain ⟨installedBody,installedPlace,installedCont,installedVa,installedClocks⟩ :=
    S02SameDestinationInstalledReturnFrame.ready id tag address len count input nonempty
      sameAllocation returnTag returnConcrete entry initial actual
  have frameTracked : done.extra.borrowTracker = some original.borrowFrame := by
    rw [ready.extra,extraEntry];exact original.frameTracked
  have donePlace : done.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by
    rw [ready.destination,placeEntry];exact installedPlace
  have doneClocks : done.extra.dataRace = none := by rw [ready.extra,extraEntry];exact installedClocks
  have valid0 : (0 : MIR.LocalId) < done.locals.size := by rw [ready.size];decide
  have local0 := Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans ready.output)
  have finalExtras : finalMachine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    change finalMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == original.destination.id) = some (original.destination.id,⟨none,#[]⟩)
    rw [copyExtras,sourceId];exact sourceExtras
  let finalThread := Classical.choose copyThread
  have finalActive : finalMachine.threads.activeThread? = some finalThread := Classical.choose_spec copyThread
  obtain ⟨updated,returnStep,_,_,_⟩ := S03ActiveSameReturnStepBounds.step options limits remaining span
    done finalMachine (GeneralBorrowRawAsMutToCopy.held copyPacket) original.borrowFrame copyTracked frameTracked
    place destination raw.parentTag raw.parent copyPacket.selected copyPacket.maximum reference.offset len sourceNode
    sourceTagged sourceNodePresent sourceHidden copyRuntime sourcePositive sourceMetadata.distinct
    (fun _ _ => currentOrder) sourceMetadata.short sourceActive
    original.returnTag original.child original.selected original.maximum returnNode currentReturnTagged returnPresent
    currentReturnSame currentReturnEdge returnHidden sourceOwned hiddenFrame copyRuntime returnPositive
    sourceMetadata.distinct (fun _ _ => currentOrder) sourceMetadata.short
    (by change (reference.offset+len).toNat ≤ original.destination.offset.toNat ∨
          (original.destination.offset+1).toNat ≤ reference.offset.toNat
        simpa only [sourceOffset,sourceLen] using original.disjoint)
    afterSourceActivity finalThread finalActive copyRace copyBackend copyGhost copyShallow #[] finalExtras (by simp)
    true (options.limits.validation-1) input.contract.model.debugOff
    (Nat.sub_add_cancel validationPositive).symm (ready.body.trans guardBody) ready.location valid0
    (congrArg LocalState.value local0) (congrArg LocalState.layout local0) doneClocks donePlace
    ((ready.continuation.trans contEntry).trans installedCont) ready.immediate
    ((ready.varargs.trans vaEntry).trans installedVa) copyUnchecked copyNoGc copyFixed
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span done finalMachine
  let sourceReleased := (copied.extra.releaseProtector raw.parentTag (GeneralBorrowRawAsMutToCopy.held copyPacket).global.protectedTags).tree
  let priorMemory := StackPopRelease.commitTree accounted.memory destination.id destination.entry sourceReleased
  let released := (sourceReleased.releaseProtector original.returnTag (GeneralBorrowRawAsMutToCopy.held copyPacket).global.protectedTags).tree
  let after := S04FinalReturnVariantsInput.afterPop #[] done accounted (GeneralBorrowRawAsMutToCopy.held copyPacket)
    original.borrowFrame priorMemory destination.id destination.entry released (finalThread.topUserRelevantFrame.getD 0)
  let finished := CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated
  have last : ExecutionMachine.step (config options (remaining+1) span) limits ()
      (Storage.withCurrent #[] done finalMachine) = (finished,.ok true) := returnStep
  have fullTrace := SuccessfulTrace.append (SuccessfulTrace.append prefixTrace guardTrace)
    (SuccessfulTrace.append copyTrace (SuccessfulTrace.Trace.next last (.refl _)))
  exact S02SameDestinationAcceptedResultJoin.finish options limits remaining span before place id tag address len count
    entry initial finished actual fullTrace rfl rfl

end
end DuplicatePrefix.S02SameDestinationAcceptedResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationAcceptedResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved same accepted Result dependency {dependency}"
