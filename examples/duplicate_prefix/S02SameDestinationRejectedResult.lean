import duplicate_prefix.S02SameDestinationRejectedResultOrder
import duplicate_prefix.S02SameDestinationRejectedResultLookup
import duplicate_prefix.S02SameDestinationRejectedResultActualLiteral
import duplicate_prefix.S02SameDestinationRejectedResultCore
import duplicate_prefix.S02SameDestinationRejectedResultLiteralActivity
import duplicate_prefix.S02SameDestinationRejectedSourceNode
import duplicate_prefix.S02SameDestinationRejectedPhysicalTransport
import duplicate_prefix.S02SameDestinationInstalledReturnFrame
import duplicate_prefix.S02SameDestinationZeroExtras
import duplicate_prefix.S02SameDestinationHiddenFrame
import duplicate_prefix.S02DisjointSharedLenLiteral
import duplicate_prefix.S02HiddenLeafActiveRelease
import duplicate_prefix.S03ActiveSameReturnStepBounds
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.DuplicatePrefixArgumentCallResult

namespace DuplicatePrefix.S02SameDestinationRejectedResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The original positive concrete same-allocation call executes Return(false)
and has successful progress on every reachable finite prefix. -/
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
    (rejected : count > len/2) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len count place := by
  obtain ⟨reference,tracker,sourceEntry,raw,entry,frame,done,machine,post,finalTree,held,child,
    actual,prefixTrace,bodyTrace,location,slotFalse,body,bodyEntry,identity,identityEntry,
    callee,calleeEntry,extra,extraEntry,placeEq,placeEntry,contEq,contEntry,vaEq,vaEntry,
    localId,localIdEntry,size,all,postMemory,postTracker,mode,runtime,⟨readPositive⟩,
    ⟨bothPositive⟩,sourceActivity,graph,rawTag,live,tracked,addresses,types,extras,ghost,shallow,race,
    backend,unchecked,noGc,fixed,thread,active,topZero,fresh,literal,rawOffset,rawLen⟩ :=
    S02SameDestinationRejectedResultActualLiteral.executes_rejected_return_frame_tag
      id tag address len count input nonempty sameAllocation returnTag returnConcrete rejected
  obtain ⟨packetFrame,packetMachine,packetActual,packet,sourceSame,sourceOffset,sourceLen,initialOrder⟩ :=
    S02SameDestinationRejectedResultCore.enters id tag address len count input nonempty sameAllocation
      returnTag returnConcrete reference
  have same : Storage.withCurrent #[] packetFrame packetMachine = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (packetActual.symm.trans actual)).2
  have frameSame := S02SeparateDestinationStateJoin.same_frame packetFrame entry packetMachine machine same
  have machineSame := S02SeparateDestinationPacketJoin.same_machine packetFrame entry packetMachine machine same
  subst packetFrame
  subst packetMachine
  have trackerEq : packet.tracker = tracker := Option.some.inj (packet.enabled.symm.trans tracked)
  obtain ⟨sourceId,sourceTag,sourceEntryEq,sourceChild,sourceNode,sourcePresent,sourceNodeTag,
    sourceHidden,sourceTagged⟩ :=
    S02SameDestinationRejectedSourceNode.preserved id tag address len count input nonempty
      sameAllocation returnTag returnConcrete reference tracker held sourceEntry raw entry machine actual
      packet sourceSame live rawTag finalTree graph
  obtain ⟨positive,nonzero,signedFits,bounds,capacity,shortRoom,nodeRoom,tagRoom⟩ :=
    S02SameDestinationSharedSiteBounds.at_actual_call id tag address len count input
      nonempty sameAllocation returnTag returnConcrete reference tracker sourceEntry entry machine actual tracked live
  have initialReturnPresent : sourceEntry.allocation.extra.nodeAt packet.child = some packet.returnNode := by
    rw [←sourceEntryEq];exact packet.returnPresent
  have initialActivity : GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra packet.child .Write
      packet.destination.offset (packet.destination.offset+1) := by
    rw [←sourceEntryEq];exact packet.activity
  have different : packet.child ≠ raw.parent := by
    rw [←sourceChild];exact packet.childrenDifferent
  have literalEq : finalTree = GeneralBorrowRawSharedToLenLiteralLedger.finalTree sourceEntry.allocation.extra tracker
      raw.parentTag raw.offset raw.len raw.tagRoom := by
    simpa only [rawTag,rawOffset,rawLen] using literal
  obtain ⟨returnActivity,returnNode,returnPresent,returnSame,returnEdge,returnLeaf,returnHidden⟩ :=
    S02SameDestinationRejectedResultLiteralActivity.preserves sourceEntry.allocation.extra tracker reference.id
      (by rw [←sourceEntryEq,←trackerEq];exact packet.runtime) raw shortRoom nodeRoom tagRoom
      packet.child packet.returnNode initialReturnPresent packet.returnLeaf packet.returnHidden different
      packet.destination.offset (packet.destination.offset+1) initialActivity
  rw [←literalEq] at returnActivity returnPresent
  have returnTagged : finalTree.indexOfTag packet.returnTag = some packet.child := by
    obtain ⟨node,present,tagEq,parentEq,hiddenEq,tagged⟩ := graph.oldNodes packet.child packet.returnNode initialReturnPresent
    rw [←packet.returnSame];exact tagged
  have parentTagged : finalTree.indexOfTag packet.destination.tag = some packet.destination.parent := by
    rw [literalEq]
    exact S02SameDestinationRejectedResultLookup.literal sourceEntry.allocation.extra tracker reference.id
      (by rw [←sourceEntryEq,←trackerEq];exact packet.runtime) raw shortRoom nodeRoom tagRoom
      packet.destination.tag packet.destination.parent (by rw [←sourceEntryEq];exact packet.destination.tagged)
  let destination := S02SameDestinationRejectedPhysicalTransport.after_body options remaining span
    packet.destination finalTree (by rw [sourceId,sourceEntryEq];exact postMemory) addresses
    (by rw [sourceEntryEq];exact graph.capacity) parentTagged
  have initialPositive : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra tracker.global.protectedTags
      (some packet.child) (some packet.selected) packet.maximum packet.destination.offset 1 := by
    rw [←sourceEntryEq,←trackerEq];exact packet.positive
  have disjoint : raw.offset.toNat+raw.len.toNat ≤ packet.destination.offset.toNat ∨
      (packet.destination.offset+1).toNat ≤ raw.offset.toNat := by
    have stop : (packet.sourceOffset+packet.sourceLen).toNat = packet.sourceOffset.toNat+packet.sourceLen.toNat := by
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt]
      have bound := packet.sourcePositive.bounds
      exact Nat.lt_of_le_of_lt bound packet.destination.entry.allocation.extra.locations.size.bytes.toNat_lt
    simpa only [rawOffset,rawLen,←sourceOffset,←sourceLen,stop] using packet.disjoint
  obtain ⟨returnPositive⟩ := S02DisjointSharedLenLiteral.destination sourceEntry.allocation.extra tracker reference.id
    (by rw [←sourceEntryEq,←trackerEq];exact packet.runtime) raw shortRoom nodeRoom tagRoom
    (some packet.child) (some packet.selected) packet.maximum packet.destination.offset 1 disjoint initialPositive
  rw [←literalEq,←graph.protections] at returnPositive
  have currentReturnSame : returnNode.tag = packet.returnTag := returnSame.trans packet.returnSame
  have currentReturnEdge : returnNode.parent = some destination.parent := returnEdge.trans packet.returnEdge
  have currentReturnHidden : returnNode.isExposed = false := returnHidden
  have sourceOther : packet.child ≠ raw.parent := different
  have afterSourceActivity := S02HiddenLeafActiveRelease.release finalTree held.global runtime
    raw.parentTag raw.parent raw.selected raw.maximum reference.offset len bothPositive sourceNode sourcePresent
    sourceHidden sourceTagged graph.distinct graph.order graph.short sourceActivity
    packet.child returnNode returnPresent returnLeaf returnHidden sourceOther
    destination.offset (destination.offset+1) returnActivity
  have sourceOwned : packet.borrowFrame.protectedTags =
      #[(destination.id,raw.parentTag),(destination.id,packet.returnTag)] := by
    change packet.borrowFrame.protectedTags = _
    rw [←sourceTag];exact packet.owned
  have hiddenFrame := S02SameDestinationHiddenFrame.of_hidden finalTree held.global packet.borrowFrame
    destination.id destination.id raw.parentTag packet.returnTag packet.child returnNode sourceOwned runtime
    raw.parent sourceNode sourceTagged sourcePresent sourceHidden returnTagged returnPresent returnHidden
  have returnOrder : ∀ valid : 0 < finalTree.roots.size,
      packet.selected ≠ finalTree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder finalTree := by
    intro valid different
    rw [literalEq]
    exact S02SameDestinationRejectedResultOrder.literal sourceEntry.allocation.extra tracker reference.id
      (by rw [←sourceEntryEq,←trackerEq];exact packet.runtime) raw shortRoom nodeRoom tagRoom
      (by rw [←sourceEntryEq];exact initialOrder)
  obtain ⟨installedBody,installedPlace,installedCont,installedVa,installedClocks⟩ :=
    S02SameDestinationInstalledReturnFrame.ready id tag address len count input nonempty
      sameAllocation returnTag returnConcrete entry machine actual
  obtain ⟨extraFrame,extraMachine,extraActual,initialExtras⟩ :=
    S02SameDestinationZeroExtras.ready id tag address len count input nonempty sameAllocation returnTag returnConcrete
  have extraSame : extraMachine = machine := congrArg (fun s : RootState => s.machine)
    (EStateM.Result.ok.inj (extraActual.symm.trans actual)).2
  have physicalId : packet.destination.id = input.contract.destination.id :=
    (S02SeparateDestinationPhysicalIdentity.original input.contract.destination packet.destination returnTag returnConcrete).1
  have finalExtras : post.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    rw [extras]
    have tick := S02SeparateDestinationTickLedger.preserved options remaining span machine
    change (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == packet.destination.id) = some (packet.destination.id,⟨none,#[]⟩)
    rw [tick.2.2.2.2.2.2.2,physicalId,←extraSame]
    exact initialExtras
  have frameTracked : done.extra.borrowTracker = some packet.borrowFrame := by rw [extraEntry];exact packet.frameTracked
  have valid0 : (0 : MIR.LocalId) < done.locals.size := by rw [size];decide
  have local0 := Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans slotFalse)
  have fuelPositive : 0 < options.limits.validation := by
    have h := input.contract.resources.configuredFuel.2.2.2
    unfold work at h;omega
  obtain ⟨updated,returnStep,_,_,_⟩ := S03ActiveSameReturnStepBounds.step options limits remaining span
    done post held packet.borrowFrame postTracker frameTracked place destination raw.parentTag raw.parent raw.selected raw.maximum
    reference.offset len sourceNode sourceTagged sourcePresent sourceHidden runtime bothPositive graph.distinct graph.order
    graph.short sourceActivity packet.returnTag packet.child packet.selected packet.maximum returnNode
    returnTagged returnPresent currentReturnSame currentReturnEdge currentReturnHidden sourceOwned hiddenFrame runtime
    returnPositive graph.distinct returnOrder graph.short
    (by
      change (reference.offset+len).toNat ≤ packet.destination.offset.toNat ∨
        (packet.destination.offset+1).toNat ≤ reference.offset.toNat
      simpa only [sourceOffset,sourceLen] using packet.disjoint) afterSourceActivity thread active race backend ghost shallow
    #[] finalExtras (by simp) false (options.limits.validation-1) input.contract.model.debugOff
    (Nat.sub_add_cancel fuelPositive).symm (bodyEntry.trans installedBody) location valid0
    (congrArg LocalState.value local0) (congrArg LocalState.layout local0)
    (by rw [extraEntry];exact installedClocks) (by rw [placeEntry];exact installedPlace)
    (contEntry.trans installedCont) all (vaEntry.trans installedVa) unchecked noGc fixed
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span done post
  let sourceReleased := (finalTree.releaseProtector raw.parentTag held.global.protectedTags).tree
  let priorMemory := StackPopRelease.commitTree accounted.memory destination.id destination.entry sourceReleased
  let released := (sourceReleased.releaseProtector packet.returnTag held.global.protectedTags).tree
  let after := S04FinalReturnVariantsInput.afterPop #[] done accounted held packet.borrowFrame priorMemory
    destination.id destination.entry released (thread.topUserRelevantFrame.getD 0)
  let finished := CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated
  have last : ExecutionMachine.step (config options (remaining+1) span) limits ()
      (Storage.withCurrent #[] done post) = (finished,.ok true) := returnStep
  have trace := SuccessfulTrace.append (SuccessfulTrace.append prefixTrace bodyTrace)
    (SuccessfulTrace.Trace.next last (.refl _))
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
    ⟨config options (remaining+1) span,limits,fun _ _ => True⟩
  have entered : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] entry machine) := by
    simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have exited : CallSafety.pastCallBoundary 1 finished := by change (0 : Nat) < 1;decide
  have terminal : ExecutionMachine.step (config options (remaining+1) span) limits () finished = (finished,.ok false) := rfl
  exact ⟨Storage.withCurrent #[] entry machine,finished,actual,trace,terminal,rfl,
    SuccessfulTrace.no_errors safety 1 _ finished entered trace exited,
    SuccessfulTrace.no_ub safety 1 _ finished entered trace exited,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩
end
end DuplicatePrefix.S02SameDestinationRejectedResult
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationRejectedResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved same rejected Result dependency {dependency}"
