import duplicate_prefix.S02AcceptedActualReturnControl
import duplicate_prefix.S02AcceptedDestinationReturnParent
import duplicate_prefix.S02SeparateDestinationInstalledReturnFrame
import duplicate_prefix.S03ActiveSeparateReturnStepBounds
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.DuplicatePrefixArgumentCallResult

namespace DuplicatePrefix.S02AcceptedActualReturnResult
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

/-- The accepted positive, distinct-concrete call executes the true Return and has NoUB. -/
theorem result
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
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len count place := by
  obtain ⟨entry,guard,done,initial,post,finalMachine,reference,sourceEntry,originalTracker,guardTracker,
    sourceRaw,guardTree,raw,originalPacket,oldNode,copyPacket,copied,actual,prefixTrace,ready,guardExtra,
    guardReturnPlace,guardContinuation,guardVa,
    guardBody,postMemory,postAddresses,postExtras,initialTracked,graph,rawTag,rawOffset,rawLen,
    copyMemory,copyAddresses,copyExtras,copyBackend,copyGhost,copyShallow,copyRace,copyFixed,
    copyUnchecked,copyNoGc,copyThread,_doneLocation,sourceId,sourceTag,sourceEntryEq,sourceChild,
    oldPresent,oldTag,oldHidden,oldTagged,sourceMetadata,selectedEq,maximumEq,copyTracked,
    protectedEq,counterGrowth,copyLive,copyRuntime,⟨copyPositive⟩,copyActivity⟩ :=
    S02AcceptedActualReturnControl.actual_return_control id tag address len count input
      nonempty different returnTag returnConcrete countPositive within
  obtain ⟨destination,destinationId,destinationEntry,destinationOffset,destinationParent,destinationRuntime,
    destinationPositive,destinationExtras⟩ :=
    S02AcceptedDestinationReturnParent.preserved id tag address len count input nonempty different
      returnTag returnConcrete entry initial post finalMachine reference sourceEntry originalTracker
      guardTracker sourceRaw guardTree originalPacket copyPacket copied actual sourceId initialTracked
      graph postMemory postAddresses copyMemory copyAddresses postExtras copyExtras protectedEq counterGrowth
  have parentEq : raw.parent = sourceRaw.parent := by
    have tagged := raw.tagged
    rw [rawTag] at tagged
    exact Option.some.inj (tagged.symm.trans oldTagged)
  have originalPresent : guardTree.nodeAt raw.parent = some oldNode := by
    rw [parentEq]
    exact oldPresent
  obtain ⟨currentNode,currentPresent,currentTag,currentExposure⟩ :=
    sourceMetadata.oldNode oldNode originalPresent
  have currentHidden : currentNode.isExposed = false := currentExposure.trans oldHidden
  have sourceTagged : copied.extra.indexOfTag raw.parentTag = some raw.parent := by
    apply sourceMetadata.tagged oldNode originalPresent
    exact oldTag.trans rawTag.symm
  have sourceOrder : ∀ valid : 0 < copied.extra.roots.size,
      copyPacket.selected ≠ copied.extra.roots[0] →
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder copied.extra := by
    intro valid differs
    apply sourceMetadata.order valid
    rw [←selectedEq]
    exact differs
  have sourceActivity : GeneralBorrowFreshActiveWithin.ActiveWithin copied.extra raw.parent .Write
      raw.offset (raw.offset+raw.len) := by
    rw [parentEq,rawOffset,rawLen]
    exact copyActivity
  let currentSource : LocalAllocation Provenance BorrowTree MiriMemoryKind := ⟨sourceEntry.kind,copied⟩
  have currentLive : finalMachine.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,currentSource) := copyLive
  have differentIds : destination.id ≠ reference.id := by
    rw [destinationId,←sourceId]
    exact originalPacket.separate
  have frameTracked : done.extra.borrowTracker = some originalPacket.borrowFrame := by
    rw [ready.extra,guardExtra]
    exact originalPacket.frameTracked
  have sourceOwned : originalPacket.borrowFrame.protectedTags =
      #[(reference.id,raw.parentTag),(destination.id,originalPacket.returnTag)] := by
    simpa only [sourceId,sourceTag,←rawTag,←destinationId] using originalPacket.owned
  obtain ⟨installedBody,installedPlace,installedCont,installedVa,installedNoClocks⟩ :=
    S02SeparateDestinationInstalledReturnFrame.ready id tag address len count input nonempty
      different returnTag returnConcrete entry initial actual
  have doneBody : done.body = RootBody.reflected.body.body := ready.body.trans (guardBody)
  have donePlace : done.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by
    rw [ready.destination,guardReturnPlace]
    exact installedPlace
  have doneCont : done.returnContinuation = .stop true :=
    (ready.continuation.trans guardContinuation).trans installedCont
  have doneVa : done.vaList = #[] := (ready.varargs.trans guardVa).trans installedVa
  have doneClocks : done.extra.dataRace = none := by rw [ready.extra,guardExtra]; exact installedNoClocks
  have valid0 : (0 : MIR.LocalId) < done.locals.size := by rw [ready.size]; decide
  have local0 := Option.some.inj (by simpa [Array.getElem?_eq_getElem valid0] using ready.output)
  have live0 : done.locals[0].value = .live (.immediate (.scalar (.fromBool true))) :=
    congrArg LocalState.value local0
  have cached0 : done.locals[0].layout = some RootCompilerFacts.boolLayout :=
    congrArg LocalState.layout local0
  let currentTracker := GeneralBorrowRawAsMutToCopy.held copyPacket
  let thread := Classical.choose copyThread
  have active : finalMachine.threads.activeThread? = some thread := Classical.choose_spec copyThread
  have fuelPositive : 0 < options.limits.validation := by
    have h := input.contract.resources.configuredFuel.2.2.2
    unfold work at h
    omega
  have emptyOutside : ∀ row ∈ (#[] : Array (Size × MemoryExtras.Entry Unit)),
      row.1.bytes.toNat < destination.offset.toNat ∨ destination.offset.toNat + 1 ≤ row.1.bytes.toNat := by simp
  obtain ⟨updated,returnStep,_,_,_⟩ :=
    S03ActiveSeparateReturnStepBounds.step options limits remaining span done finalMachine currentTracker
      originalPacket.borrowFrame copyTracked frameTracked place destination reference.id currentSource
      differentIds currentLive raw.parentTag raw.parent copyPacket.selected copyPacket.maximum
      raw.offset raw.len currentNode sourceTagged currentPresent currentHidden copyRuntime copyPositive
      sourceMetadata.distinct sourceOrder sourceMetadata.short sourceActivity
      originalPacket.returnTag originalPacket.child originalPacket.selected originalPacket.maximum
      originalPacket.returnNode
      (by rw [destinationEntry]; exact originalPacket.returnTagged)
      (by rw [destinationEntry]; exact originalPacket.returnPresent)
      originalPacket.returnSame
      (by rw [destinationParent]; exact originalPacket.returnEdge)
      originalPacket.returnHidden
      sourceOwned
      (by rw [destinationEntry]; exact originalPacket.hiddenFrame)
      destinationRuntime destinationPositive
      (by rw [destinationEntry]; exact originalPacket.distinct)
      (by rw [destinationEntry]; exact originalPacket.order)
      (by rw [destinationEntry]; exact originalPacket.short)
      (by rw [destinationEntry,destinationOffset]; exact originalPacket.activity)
      thread active copyRace copyBackend copyGhost copyShallow #[] destinationExtras emptyOutside
      true (options.limits.validation-1) input.contract.model.debugOff
      (Nat.sub_add_cancel fuelPositive).symm doneBody ready.location valid0 live0 cached0
      doneClocks donePlace doneCont ready.immediate doneVa copyUnchecked copyNoGc copyFixed
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span done finalMachine
  let sourceReleased := (currentSource.allocation.extra.releaseProtector raw.parentTag currentTracker.global.protectedTags).tree
  let priorMemory := StackPopRelease.commitTree accounted.memory reference.id currentSource sourceReleased
  let released := (destination.entry.allocation.extra.releaseProtector originalPacket.returnTag currentTracker.global.protectedTags).tree
  let after := S04FinalReturnVariantsInput.afterPop #[] done accounted currentTracker originalPacket.borrowFrame
    priorMemory destination.id destination.entry released (thread.topUserRelevantFrame.getD 0)
  let finished := CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated
  have last : ExecutionMachine.step (config options (remaining+1) span) limits ()
      (Storage.withCurrent #[] done finalMachine) = (finished,.ok true) := returnStep
  have trace := SuccessfulTrace.append prefixTrace (SuccessfulTrace.Trace.next last (.refl _))
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
    ⟨config options (remaining+1) span,limits,fun _ _ => True⟩
  have entered : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] entry initial) := by
    simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have exited : CallSafety.pastCallBoundary 1 finished := by
    change (0 : Nat) < 1
    decide
  have terminal : ExecutionMachine.step (config options (remaining+1) span) limits () finished = (finished,.ok false) := rfl
  exact ⟨Storage.withCurrent #[] entry initial,finished,actual,trace,terminal,rfl,
    SuccessfulTrace.no_errors safety 1 _ finished entered trace exited,
    SuccessfulTrace.no_ub safety 1 _ finished entered trace exited,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.S02AcceptedActualReturnResult

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02AcceptedActualReturnResult.result) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved accepted Return Result dependency {dependency}"
