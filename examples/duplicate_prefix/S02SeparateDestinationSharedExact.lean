import duplicate_prefix.S02SeparateDestinationExact
import duplicate_prefix.S02ConcreteCallPreamble
import duplicate_prefix.S02ConcreteSharedSourceRegistration
import duplicate_prefix.S02SeparateDestinationSourceLive
import duplicate_prefix.S05ConcreteEntryBridge
import duplicate_prefix.S02ConcreteSourceCurrent
import duplicate_prefix.GeneralBorrowRawFnEntryOrder

namespace DuplicatePrefix.S02SeparateDestinationSharedExact
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Exact source allocation geometry and tag counter accompany the actual
call's shared-reference input. This closes the storage/headroom transport
needed by the slice-length call. -/
theorem after_exact
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (tracker : MachineHooks.BorrowState)
      (installed : CompilerFrameContext.ActualFrame)
      (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (child : UniIndex)
      (raw : GeneralBorrowRawShared.Input sourceEntry.allocation.extra tracker.global),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed post) ∧
      post.borrowTracker = some tracker ∧
      post.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) ∧
      sourceEntry = {reference.entry with allocation := (reference.entry.allocation.setExtra
        (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
          reference.tracker tag reference.offset len))} ∧
      tracker.global.nextPointerTag.value.toNat = reference.tracker.global.nextPointerTag.value.toNat + 2 ∧
      raw.parentTag = reference.tracker.global.nextPointerTag ∧
      raw.parent = child ∧ raw.offset = reference.offset ∧ raw.len = len ∧
      DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra tracker.global ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra child .Write
        reference.offset (reference.offset+len) := by
  obtain ⟨reference,firstFresh,_argument,destination,secondFresh,tree,updated,_protect,_bytes,_length,_mutable,
      _unusedFinal,_unusedFinish⟩ :=
    S02SeparateDestinationExact.concrete_after_argument_finish id tag address len count input nonempty
      different returnTag returnConcrete limits.retag
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker firstFresh
    reference.id reference.entry tag reference.offset len
  let raw := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone raw adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  have finishShape := S02PositiveFinishFrame.after_destination_registration raw
    (RawRootInvocation.locals before place input.contract.model.noDataRace)
    adjusted count reference.id destination.id reference.tracker.global.nextPointerTag
    destination.tracker.global.nextPointerTag
  obtain ⟨body,frameSize,dead,noClocks⟩ := finishShape
  have finish := RootEntryFinish.actual_finish options limits (remaining+1) span #[] protectedFrame after.machine
    body frameSize (dead ⟨0,by decide⟩ (by omega) (Or.inl rfl))
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
  have tail : RootEntryTail.tail h place (Storage.withCurrent #[] frame current) =
      .ok () (Storage.withCurrent #[] installed after.machine) := by
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
      RootEntryFinish.finish h) (Storage.withCurrent #[] changed current) =
        .ok () (Storage.withCurrent #[] installed after.machine)
    simp only [bind,EStateM.bind]
    rw [_protect]
    change RootEntryFinish.finish
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      (Storage.withCurrent #[] protectedFrame after.machine) =
        .ok () (Storage.withCurrent #[] installed after.machine)
    exact finish
  obtain ⟨preambleAfter,preambleArg,preambleContinue⟩ :=
    S02ConcreteCallPreamble.prefix_and_continuation id tag address len count input nonempty
  have sameAfter : preambleAfter = Storage.withCurrent #[] frame current := by
    have resultEq := preambleArg.symm.trans _argument
    exact (EStateM.Result.ok.inj resultEq).2
  have actualCall := preambleContinue (Storage.withCurrent #[] installed after.machine) (sameAfter ▸ tail)
  let next := TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  have tracked : after.machine.borrowTracker = some next := rfl
  obtain ⟨same,raw0,parent,offset,length,_source,_selected,_maximum,initialRuntime⟩ :=
    S05ConcreteEntryBridge.from_positive id tag address len reference
      input.contract.runtime input.contract.resources
  let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra sourceTree}
  have treeEq : sourceTree = GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
      reference.tracker raw0.parentTag raw0.offset raw0.len := by
    rw [parent,offset,length]
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have nodeRoom : reference.entry.allocation.extra.nodes.size + 2 < 65536 := by
    have room : reference.entry.allocation.extra.nodes.size + 16 < 65536 := by
      simpa only [Prod.snd] using input.contract.resources.nodeRoom (reference.id,reference.entry) member
    omega
  have refTracker : reference.tracker = input.contract.tracker :=
    Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
  have tagMargin : reference.tracker.global.nextPointerTag.value.toNat + 3 < 18446744073709551616 := by
    rw [refTracker]
    have room := input.contract.resources.tagRoom
    omega
  obtain ⟨child,firstRaw,firstTag,firstParent,firstOffset,firstLen,firstRuntime,⟨firstPositive⟩,firstActivity⟩ :=
    S02ConcreteSharedSourceInput.after_argument reference.entry.allocation.extra reference.tracker
      reference.id initialRuntime raw0 nodeRoom tagMargin
  have destTracker : destination.tracker =
      ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,reference.tracker.retagMode⟩ :=
    Option.some.inj (destination.enabled.symm.trans (show current.borrowTracker =
      some ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,reference.tracker.retagMode⟩ from rfl))
  have firstGlobal : (TypedBorrowSteps.registeredGlobal
      (ReferenceBorrowDriver.allocatedTracker reference.tracker raw0.tagRoom)
      reference.tracker.global.nextPointerTag) = destination.tracker.global := by
    rw [destTracker]
    rfl
  have sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts sourceTree destination.tracker.global := by
    simpa only [treeEq,firstGlobal] using firstRuntime
  have sourcePositive : DuplicatePrefixBorrowAuthorization.Positive sourceTree
      destination.tracker.global.protectedTags (some child) (some raw0.selected) raw0.maximum
      raw0.offset raw0.len := by
    simpa only [treeEq,firstGlobal] using firstPositive
  have sourceActivity : GeneralBorrowFreshActiveWithin.ActiveWithin sourceTree child .Write
      raw0.offset (raw0.offset+raw0.len) := by
    simpa only [treeEq] using firstActivity
  have secondMargin : destination.tracker.global.nextPointerTag.value.toNat + 2 < 18446744073709551616 := by
    rw [destTracker]
    have successor := GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag firstFresh
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag firstFresh).value.toNat =
      reference.tracker.global.nextPointerTag.value.toNat + 1 at successor
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag firstFresh).value.toNat + 2 <
      18446744073709551616
    rw [successor]
    omega
  have orderAll : GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceTree := by
    have oldOrder := input.contract.runtime.parent_order reference.id reference.entry reference.live
    have currentOrder := GeneralBorrowRawFnEntryOrder.order reference.entry.allocation.extra reference.tracker
      {} reference.id initialRuntime raw0 oldOrder
    rw [←treeEq] at currentOrder
    exact currentOrder
  let correctedRaw : GeneralBorrowRawShared.Input sourceTree destination.tracker.global := {
    parentTag := reference.tracker.global.nextPointerTag
    parent := child
    selected := raw0.selected
    maximum := raw0.maximum
    offset := raw0.offset
    len := raw0.len
    tagged := by
      rw [treeEq,←firstTag,←firstParent]
      exact firstRaw.tagged
    positive := Classical.choice (GeneralBorrowReadRowRange.of_positive sourceTree
      destination.tracker.global.protectedTags child raw0.selected raw0.maximum raw0.offset raw0.len sourcePositive)
    distinct := by rw [treeEq]; exact firstRaw.distinct
    order := by intro _ _; exact orderAll
    short := by rw [treeEq]; exact firstRaw.short
    nodeRoom := by rw [treeEq]; exact firstRaw.nodeRoom
    tagRoom := by rw [←firstGlobal]; exact firstRaw.tagRoom }
  obtain ⟨secondRuntime,⟨secondPositive⟩,secondRaw,secondTag,secondParent,secondOffset,secondLen,secondActivity⟩ :=
    S02ConcreteSharedSourceRegistration.after_destination sourceTree destination.tracker.global
      owned destination.id secondFresh secondMargin sourceRuntime correctedRaw sourcePositive sourceActivity
  have separate : destination.id ≠ reference.id := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have pointer := congrArg (fun p : Pointer (Option Provenance) => p.provenance) physical
    simp only [Pointer.withOptionalProvenance] at pointer
    have concrete : destination.pointer.provenance =
        .concrete input.contract.destination.id returnTag :=
      (Option.some.inj pointer).trans returnConcrete
    have binding := destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
    have destId : destination.id = input.contract.destination.id := binding.1.symm
    simpa only [destId,same] using Ne.symm different
  obtain ⟨_currentChild,_currentRaw,_same,_parent,_offset,_length,sourceLive,_enabled,_runtime,_positive⟩ :=
    S02ConcreteSourceCurrent.source_ready_at_actual_current id tag address len input reference firstFresh
  have liveAfter : after.machine.memory.live.find? (fun row => row.1 == reference.id) =
      some (reference.id,sourceEntry) := by
    rw [S02SeparateDestinationSourceLive.source_live_after_protect current place destination #[]
      changed owned secondFresh tree updated reference.id separate]
    exact sourceLive
  have globalEq : next.global =
      (GeneralBorrowFnEntryRegistration.registered destination.tracker.global owned destination.id secondFresh).1 := rfl
  change DuplicatePrefixBorrowContract.RuntimeFacts sourceTree next.global at secondRuntime
  change GeneralBorrowRawShared.Input sourceTree next.global at secondRaw
  have sameParent : secondRaw.parent = child := secondParent
  have sameOffset : secondRaw.offset = reference.offset := secondOffset.trans offset
  have sameLen : secondRaw.len = len := secondLen.trans length
  have sameTag : secondRaw.parentTag = reference.tracker.global.nextPointerTag := secondTag
  have sourceActivity : GeneralBorrowFreshActiveWithin.ActiveWithin sourceTree child .Write
      reference.offset (reference.offset+len) := by
    simpa [correctedRaw,offset,length] using secondActivity
  have counter : next.global.nextPointerTag.value.toNat =
      reference.tracker.global.nextPointerTag.value.toNat + 2 := by
    have firstStep := GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag firstFresh
    have secondStep := GenericFunctionEntryNumerics.successor_value destination.tracker.global.nextPointerTag secondFresh
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag firstFresh).value.toNat =
      reference.tracker.global.nextPointerTag.value.toNat + 1 at firstStep
    change (TypedRetagEmpty.successorTag destination.tracker.global.nextPointerTag secondFresh).value.toNat =
      destination.tracker.global.nextPointerTag.value.toNat + 1 at secondStep
    change (TypedRetagEmpty.successorTag destination.tracker.global.nextPointerTag secondFresh).value.toNat = _
    rw [secondStep,destTracker]
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag firstFresh).value.toNat + 1 = _
    omega
  exact ⟨reference,next,installed,after.machine,sourceEntry,child,secondRaw,actualCall,tracked,liveAfter,
    rfl,counter,sameTag,sameParent,sameOffset,sameLen,secondRuntime,sourceActivity⟩

end
end DuplicatePrefix.S02SeparateDestinationSharedExact

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationSharedExact.after_exact) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate machine settings dependency {dependency}"
