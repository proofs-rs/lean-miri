import duplicate_prefix.S02WildcardPositiveIdUnique
import duplicate_prefix.S02WildcardSameDestinationInitAfterArgument
import duplicate_prefix.S02WildcardSourceWildcardZeroControl
import duplicate_prefix.S02WildcardCallPreamble
import duplicate_prefix.S02WildcardReturnSameProtect
import duplicate_prefix.S02WildcardReturnSameSourceActivityPacket
import duplicate_prefix.S02WildcardReturnSameStep
import duplicate_prefix.S04ZeroCountBodyActiveWildcardBounds
import duplicate_prefix.S02HiddenLeafActiveRelease
import duplicate_prefix.S02SameDestinationHiddenFrame
import duplicate_prefix.S02ConcreteSourceWildcardZeroControl
import duplicate_prefix.S02ConcreteSourceReleasePacket
import duplicate_prefix.S02FnEntryFreshNode
import duplicate_prefix.S02SameDestinationLiveTransport
import duplicate_prefix.S02WildcardReturnRootNotPrimary
import duplicate_prefix.S03ReturnWildcardMetadata
import duplicate_prefix.S02PositiveFinishFrame
import duplicate_prefix.RootEntryFinish
import duplicate_prefix.RootZeroCompletePrefix
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.DuplicatePrefixArgumentCallResult
namespace DuplicatePrefix.S02WildcardReturnSameZeroResultWildcard
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Positive wildcard source and wildcard return destination in the same
allocation execute the original count-zero Call, MIR body, and physical Return. -/
theorem result
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard) :
    ∃ reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len,
      reference.id = input.contract.destination.id →
      DuplicatePrefixArgumentCallResult.Result options limits remaining span before
        (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len 0 place := by
  obtain ⟨reference,output,firstFresh,run,argument⟩ := S02WildcardArgumentScope.argument_body address len 0 input nonempty
  refine ⟨reference,?_⟩
  intro sameAllocation
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker firstFresh reference.id reference.entry output.child.tree
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let args := RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted ({} : FrameState) reference.id reference.tracker.global.nextPointerTag) 0
  let changed := {args.frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let original := input.contract.destination
  have entryEq : reference.entry = original.entry := by
    have live := reference.live
    rw [sameAllocation] at live
    exact congrArg Prod.snd (Option.some.inj (live.symm.trans original.live))
  have originalTracker : original.tracker = reference.tracker := Option.some.inj (original.enabled.symm.trans reference.enabled)
  obtain ⟨_,_,_,initialPositive,initialRuntime,initialDistinct,initialShort,initialRoom,initialFresh⟩ :=
    S05WildcardEntryBridge.from_positive address len reference input.contract.runtime.toState input.contract.resources
  have originalPositive : DuplicatePrefixBorrowAuthorization.Positive reference.entry.allocation.extra reference.tracker.global.protectedTags
      original.source original.selectedRoot original.maximum original.offset 1 := by rw [entryEq,←originalTracker];exact original.borrow
  have separation := S02WildcardSameDestinationInitInput.disjoint address len input nonempty reference sameAllocation
  have outside : reference.offset.toNat+len.toNat ≤ original.offset.toNat ∨ (original.offset+1).toNat ≤ reference.offset.toNat := by
    rcases separation with left | right
    · exact Or.inl left
    · exact Or.inr (Nat.le_trans (by simp only [UInt64.toNat_add];exact Nat.mod_le _ _) right)
  obtain ⟨otherOutput,otherRun,⟨originalAfter⟩,capacity,oldNodes,oldTags⟩ :=
    S02WildcardSameDestinationRootOperation.operation_destination reference.entry.allocation.extra reference.tracker.global
      ({} : FrameState) reference.id initialRuntime reference.offset len initialPositive initialDistinct initialShort initialRoom initialFresh
      original.source original.selectedRoot original.maximum original.offset 1 outside originalPositive
  have sameOutput : otherOutput = output := Except.ok.inj (otherRun.symm.trans run)
  subst otherOutput
  obtain ⟨sourceRuntime,sourceRoots,sourceOrder,sourceRoom,secondRoom,_capacity,sourceChild,sourceNode,sourceTagged,sourcePresent,
    sourceSame,_sourceParent,sourceLeaf,sourceHidden,⟨sourcePositive⟩,sourceActive,globalEq⟩ :=
    S02WildcardSameDestinationInitReady.facts address len input reference output firstFresh run
  rw [globalEq] at originalAfter
  let destination : DuplicatePrefixReturnPlaceInput.Input current place := {
    tracker := ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,reference.tracker.retagMode⟩,enabled := rfl,
    pointer := original.pointer,physicalPointer := original.physicalPointer,layout := original.layout,aligned := original.aligned,
    id := original.id,entry := {original.entry with allocation := original.entry.allocation.setExtra output.child.tree},
    base := original.base,offset := original.offset,capacity := original.capacity,
    live := by
      change (RetagEntry.updatedMemory machine.memory reference.id reference.entry output.child.tree).live.find? (fun row => row.1 == original.id) = _
      rw [←sameAllocation,←entryEq];exact MemoryCopyBridge.live_lookup_replaced _ _ _,
    cachedBase := by
      change machine.user.addresses.baseAddr.find? (fun row => row.allocId == original.id) = _
      rw [(RawRootInvocation.preservation #[] before).2.2.2.1];exact original.cachedBase,
    pointerAddress := original.pointerAddress,nonnull := original.nonnull,addressFits := original.addressFits,bounds := original.bounds,
    size := original.size,bytes := original.bytes,mutable := original.mutable,maskValid := original.maskValid,maskLength := original.maskLength,
    provenanceMap := original.provenanceMap,borrowSize := by change output.child.tree.locations.size.bytes = original.capacity;rw [capacity,entryEq];exact original.borrowSize,
    source := original.source,selectedRoot := original.selectedRoot,maximum := original.maximum,
    binding := by
      change DuplicatePrefixReferenceInput.Binding machine.user.addresses original.pointer original.id original.base _ _ original.source
      have bind := original.binding
      simp only [DuplicatePrefixReferenceInput.Binding,show original.pointer.provenance = .wildcard from returnWildcard] at bind ⊢
      rw [(RawRootInvocation.preservation #[] before).2.2.2.1]
      exact bind,
    borrow := originalAfter }
  have destId : destination.id = input.contract.destination.id := rfl
  have sameId : destination.id = reference.id := sameAllocation.symm
  have destOffset : destination.offset = input.contract.destination.offset := rfl
  have destEntry : destination.entry = {reference.entry with allocation := reference.entry.allocation.setExtra output.child.tree} := by change {original.entry with allocation := original.entry.allocation.setExtra output.child.tree} = _;rw [entryEq]
  have wildcard : destination.pointer.provenance = .wildcard := returnWildcard
  have frameBorrow : changed.extra.borrowTracker = some owned := by
    simp only [changed,args,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,RootFrameData.cache,
      RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,owned]
  have extras : current.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    change machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _
    rw [(RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2,destId];exact input.return_extras
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra destination.tracker.global := sourceRuntime
  have roots : destination.entry.allocation.extra.roots.toList.Nodup := sourceRoots
  have initialOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder destination.entry.allocation.extra := sourceOrder
  have headroom : destination.entry.allocation.extra.nodes.size+1 < 65536 := sourceRoom
  have secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615 := secondRoom
  have model := S02WildcardSeparateDestinationReady.model_after_argument input reference output firstFresh
  obtain ⟨tree,updated,protect,extra,bytes,length,mutable,_mask,_maskLen,_pointerBounds,_capacity2,
    postRuntime,short,distinct,order,exposed,oldTag,child,tagged,rootPush,⟨returnPositive⟩,returnActivity,returnNode,returnPresent,returnSame,parentless,leaf,returnHidden⟩ :=
    S03ReturnWildcardProtectionRawOtherTags.invoke_other_tags (options := options) (remaining := remaining+1) (span := span)
      limits.retag current model place destination runtime roots initialOrder headroom secondFresh wildcard #[] changed owned frameBorrow #[] extras (by simp)
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let installed := CallEntryFacts.doneRootFrame
    {TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag with location := .unwinding ⟨559⟩}
  let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh) destination.tracker.global.nextPointerTag
  let written := (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag)
    (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
  have trackerEq : destination.tracker = ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,reference.tracker.retagMode⟩ := rfl
  have beforeTagged : destination.entry.allocation.extra.indexOfTag reference.tracker.global.nextPointerTag = some sourceChild := sourceTagged
  have beforePresent : destination.entry.allocation.extra.nodeAt sourceChild = some sourceNode := sourcePresent
  have beforeActive : GeneralBorrowFreshActiveWithin.ActiveWithin destination.entry.allocation.extra sourceChild .Write reference.offset (reference.offset+len) := sourceActive
  have beforePositive : DuplicatePrefixBorrowAuthorization.Positive destination.entry.allocation.extra destination.tracker.global.protectedTags
      (some sourceChild) (some sourceChild) (some reference.tracker.global.nextPointerTag) reference.offset len := sourcePositive
  have stopEq : (reference.offset+len).toNat = reference.offset.toNat+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt];exact Nat.lt_of_le_of_lt reference.borrow.bounds reference.entry.allocation.extra.locations.size.bytes.toNat_lt
  have disjoint : destination.offset.toNat+1 ≤ reference.offset.toNat ∨ (reference.offset+len).toNat ≤ destination.offset.toNat := by rw [destOffset,stopEq];exact separation.symm
  obtain ⟨other,otherProtect,otherExtra,maskWf,maskLen,pointerBounds,⟨sourceAfter⟩,sourceActivity,sourceNodeAfter,sourceTags,
    sourceRuntimeAfter,sourceCapacity,otherBytes,otherLen,otherMutable⟩ := S02WildcardReturnSameSourceActivityPacket.invoke
    (options := options) (remaining := remaining+1) (span := span) limits.retag current model place destination runtime roots headroom secondFresh wildcard
    #[] changed owned frameBorrow #[] extras (by simp) sourceChild sourceChild (some reference.tracker.global.nextPointerTag) reference.offset len disjoint beforePositive
    sourceNode beforePresent sourceLeaf sourceHidden beforeActive
  have sameState := (EStateM.Result.ok.inj (protect.symm.trans otherProtect)).2
  have live1 : after.machine.memory.live.find? (fun row => row.1 == destination.id) = some (destination.id,{destination.entry with allocation := updated}) :=
    MemoryCopyBridge.live_lookup_replaced _ _ _
  let otherTree := ((destination.entry.allocation.extra.performBorrowAccessRange .wildcard (Size.ofBytes destination.offset) (Size.ofBytes 1) .Read
    (GeneralBorrowFnEntryRegistration.registered destination.tracker.global owned destination.id secondFresh).1.protectedTags .VisitChildrenOfAccessed).tree.newChild
    (Size.ofBytes destination.offset) .wildcard destination.tracker.global.nextPointerTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree
  have live2 : (S04ProtectUninit.finished current place destination #[] changed owned secondFresh otherTree other).machine.memory.live.find?
      (fun row => row.1 == destination.id) = some (destination.id,{destination.entry with allocation := other}) := MemoryCopyBridge.live_lookup_replaced _ _ _
  have updatedEq : updated = other := by
    change (S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated).machine.memory.live.find? (fun row => row.1 == destination.id) = _ at live1
    rw [sameState] at live1
    exact congrArg (fun row => row.2.allocation) (Option.some.inj (live1.symm.trans live2))
  rw [←updatedEq] at maskWf maskLen pointerBounds sourceAfter sourceActivity sourceNodeAfter sourceTags sourceRuntimeAfter sourceCapacity
  have capacity : written.locations.size = destination.entry.allocation.extra.locations.size := by
    change (tree.performBorrowAccessRange (.concrete destination.tracker.global.nextPointerTag) (Size.ofBytes destination.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree.locations.size = _
    rw [←extra]
    exact sourceCapacity
  let physical := S03ReturnWildcardMetadata.of_protection destination wildcard #[] changed owned secondFresh tree updated written extra bytes length mutable maskWf maskLen pointerBounds capacity
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag
  have finishShape := S02PositiveFinishFrame.after_destination_registration root (RawRootInvocation.locals before place input.contract.model.noDataRace)
    adjusted 0 reference.id destination.id reference.tracker.global.nextPointerTag destination.tracker.global.nextPointerTag
  obtain ⟨finishBody,finishSize,finishDead,finishClocks⟩ := finishShape
  have finish := RootEntryFinish.actual_finish options limits (remaining+1) span #[] protectedFrame after.machine finishBody finishSize
    (finishDead ⟨0,by decide⟩ (by omega) (Or.inl rfl)) (finishDead ⟨6,by decide⟩ (by omega) (Or.inr (Or.inl rfl)))
    (finishDead ⟨13,by decide⟩ (by omega) (Or.inr (Or.inr (Or.inl rfl)))) (finishDead ⟨14,by decide⟩ (by omega) (Or.inr (Or.inr (Or.inr rfl)))) finishClocks
  let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
  have localSpan := CallEntryLocals.root_span0 options limits (remaining+1) span #[] args.frame current (by rfl) (by rfl) (by rfl)
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] args.frame current
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] args.frame changed current
  have compat : h.checkArgumentCompat () RootCompilerFacts.rootAbi.ret RootCompilerFacts.rootAbi.ret (Storage.withCurrent #[] changed current) = .ok true (Storage.withCurrent #[] changed current) := by
    change (config options (remaining+1) span).calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [(actual_fields options () (remaining+1) span).callCompiler];exact CallEntryFacts.root_return_argument_compat _ options.compatibilityBudget _
  have tail : RootEntryTail.tail h place (Storage.withCurrent #[] args.frame current) = .ok () (Storage.withCurrent #[] installed after.machine) := by
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
    change (do TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag limits.retag place;RootEntryFinish.finish h)
      (Storage.withCurrent #[] changed current) = .ok () (Storage.withCurrent #[] installed after.machine)
    simp only [bind,EStateM.bind]
    rw [protect]
    exact finish
  obtain ⟨prefixState,preambleArg,preambleContinue⟩ := S02WildcardCallPreamble.prefix_and_continuation address len 0 input nonempty
  have sameAfter : prefixState = Storage.withCurrent #[] args.frame current := (EStateM.Result.ok.inj (preambleArg.symm.trans argument)).2
  have actual := preambleContinue _ (sameAfter ▸ tail)
  obtain ⟨settings⟩ := S02WildcardSourceWildcardZeroControl.at_protection address len input reference output firstFresh destination destId secondFresh tree updated
  let tracker := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh) destination.tracker.global.nextPointerTag
  let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
  have enabled : after.machine.borrowTracker = some tracker := rfl
  have settingsTracker : settings.tracker = tracker := Option.some.inj (settings.enabled.symm.trans enabled)
  have mode : tracker.retagMode = .Default := by rw [←settingsTracker];exact settings.mode
  have frameTracked : installed.extra.borrowTracker = some borrowFrame := rfl
  have sourceTaggedAfter : updated.extra.indexOfTag reference.tracker.global.nextPointerTag = some sourceChild := sourceTags _ _ beforeTagged
  have sourcePositiveAfter : DuplicatePrefixBorrowAuthorization.Positive updated.extra tracker.global.protectedTags
      (some sourceChild) (some sourceChild) (some reference.tracker.global.nextPointerTag) reference.offset len := sourceAfter
  have sourcePresentAfter : updated.extra.nodeAt sourceChild = some sourceNode := sourceNodeAfter
  have runtimeAfter : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra tracker.global := by rw [extra];exact postRuntime
  have taggedAfter : updated.extra.indexOfTag destination.tracker.global.nextPointerTag = some child := by rw [extra];exact tagged
  have returnPresentAfter : updated.extra.nodeAt child = some returnNode := by rw [extra];exact returnPresent
  have returnPositiveAfter : DuplicatePrefixBorrowAuthorization.Positive updated.extra tracker.global.protectedTags
      (some child) (some child) (some destination.tracker.global.nextPointerTag) destination.offset 1 := by rw [extra];exact returnPositive.base
  have nextDifferent : destination.tracker.global.nextPointerTag ≠ reference.tracker.global.nextPointerTag := by
    intro equal
    have successor := GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag firstFresh
    have values := congrArg (fun t : BorTag => t.value.toNat) equal
    rw [trackerEq] at values
    change (TypedRetagEmpty.successorTag reference.tracker.global.nextPointerTag firstFresh).value.toNat = _ at values
    omega
  have different : child ≠ sourceChild := by
    intro equal
    rw [equal] at returnPresentAfter
    have sameNode := Option.some.inj (returnPresentAfter.symm.trans sourcePresentAfter)
    exact nextDifferent (returnSame.symm.trans ((congrArg TreeNode.tag sameNode).trans sourceSame))
  have ownedTags : borrowFrame.protectedTags = #[(physical.id,reference.tracker.global.nextPointerTag),(physical.id,destination.tracker.global.nextPointerTag)] := by
    change #[(reference.id,reference.tracker.global.nextPointerTag),(destination.id,destination.tracker.global.nextPointerTag)] = _
    change #[(reference.id,reference.tracker.global.nextPointerTag),(destination.id,destination.tracker.global.nextPointerTag)] = #[(destination.id,reference.tracker.global.nextPointerTag),(destination.id,destination.tracker.global.nextPointerTag)]
    simp only [sameId]
  have hiddenFrame := S02SameDestinationHiddenFrame.of_hidden updated.extra tracker.global borrowFrame
    physical.id physical.id reference.tracker.global.nextPointerTag destination.tracker.global.nextPointerTag child returnNode ownedTags runtimeAfter
    sourceChild sourceNode sourceTaggedAfter sourcePresentAfter sourceHidden taggedAfter returnPresentAfter returnHidden
  have initialWildcard : destination.source = none := by
    have b := destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,wildcard] at b;exact b.1
  have rootsNonempty := destination.borrow.wildcardRoot initialWildcard
  have notPrimary := S02WildcardReturnRootNotPrimary.after_push destination.entry.allocation.extra written child rootsNonempty rootPush distinct
  have distinctAfter : updated.extra.roots.toList.Nodup := by rw [extra];exact distinct
  have orderAfter : GeneralBorrowWildcardParentTagOrder.ParentTagOrder updated.extra := by rw [extra];exact order
  have shortAfter : updated.extra.nodes.size < 65536 := by rw [extra];exact short
  have afterActivity := S02HiddenLeafActiveRelease.release updated.extra tracker.global runtimeAfter reference.tracker.global.nextPointerTag
    sourceChild sourceChild (some reference.tracker.global.nextPointerTag) reference.offset len sourcePositiveAfter sourceNode sourcePresentAfter sourceHidden sourceTaggedAfter
    distinctAfter (fun _ _ => orderAfter) shortAfter sourceActivity child returnNode returnPresentAfter leaf returnHidden different
    destination.offset (destination.offset+1) (by rw [extra];exact returnActivity)
  have metadata := PositiveRootInstalledFrame.metadata root adjusted 0 {} reference.id reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag
  have frameEq : installed = PositiveRootInstalledFrame.installed root adjusted 0 {} reference.id reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag := rfl
  have frameSize : installed.locals.size = 25 := by rw [frameEq];exact PositiveRootInstalledFrame.size _ _ _ _ _ _ _ _
  have body : installed.body = RootBody.reflected.body.body := by rw [frameEq];exact metadata.1.trans root.body
  have identity : installed.bodyIdentity = RootBody.reflected.body.identity := by rw [frameEq];exact metadata.2.1.trans root.identity
  have callee : installed.functionInstance = RootBody.reflected.functionInstance := by rw [frameEq];exact metadata.2.2.1.trans root.callee
  have location : installed.location = .mir ⟨0,0⟩ := by rw [frameEq];exact metadata.2.2.2.2.2.2.2.2
  have noClocks : installed.extra.dataRace = none := by rw [frameEq];exact metadata.2.2.2.2.2.2.1.trans root.noClocks
  have returnPlace : installed.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by rw [frameEq,metadata.2.2.2.2.1];rfl
  have continuation : installed.returnContinuation = .stop true := by rw [frameEq];exact metadata.2.2.2.1
  have varargs : installed.vaList = #[] := by rw [frameEq,metadata.2.2.2.2.2.1];rfl
  have all : CopyHelperCleanup.AllImmediate installed := by rw [frameEq];exact PositiveRootInstalledFrame.immediate root (RawRootInvocation.locals before place input.contract.model.noDataRace) _ _ _ _ _ _ _
  have slots := PositiveRootInstalledFrame.slot_option root (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted 0 {} reference.id reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag
  have cell (i : Fin 25) : installed.locals[i.val]'(by rw [frameSize];exact i.isLt) =
      if 14=i.val ∨ 13=i.val ∨ 6=i.val ∨ 0=i.val then ⟨.live (.immediate .uninit),none⟩
      else if 2=i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))),some RootCompilerFacts.usizeLayout⟩
      else if 1=i.val then ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩ else ⟨.dead,none⟩ := by
    exact Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];exact i.isLt)).symm.trans (by rw [frameEq];exact slots i))
  obtain ⟨done,bodyTrace,fb,fi,ff,fe,frp,frc,fva,fli,fsz,doneLocation,done0,allDone⟩ := RootZeroCompletePrefix.reaches_return
    options limits remaining span (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
    settings.debugOff settings.fuel settings.validationFuel installed after.machine body identity callee location frameSize
    (by simpa using congrArg LocalState.value (cell ⟨0,by decide⟩)) (by simpa using congrArg LocalState.layout (cell ⟨0,by decide⟩))
    (by simpa using congrArg LocalState.value (cell ⟨3,by decide⟩)) (by simpa using congrArg LocalState.value (cell ⟨4,by decide⟩))
    (by simpa using congrArg LocalState.value (cell ⟨5,by decide⟩)) (by simpa using congrArg LocalState.layout (cell ⟨4,by decide⟩))
    (by simpa using congrArg LocalState.layout (cell ⟨5,by decide⟩)) (by simpa using congrArg LocalState.value (cell ⟨2,by decide⟩))
    (by simpa using congrArg LocalState.layout (cell ⟨2,by decide⟩)) noClocks all tracker enabled mode settings.ghost settings.shallow settings.unchecked settings.noGc settings.fixed
  let first := RootZeroCompleteState.tick options remaining span after.machine
  let current2 := RootZeroCompleteState.tick options remaining span first
  let d1 := S04ZeroCountBodyActiveWildcardBounds.tick_destination options remaining span after.machine place physical
  let d2 := S04ZeroCountBodyActiveWildcardBounds.tick_destination options remaining span first place d1
  have fields1 := RootZeroInvocationState.tick_fields options remaining span after.machine
  have fields2 := RootZeroInvocationState.tick_fields options remaining span first
  have flags1 := RootZeroCompleteState.tick_flags options remaining span after.machine
  have flags2 := RootZeroCompleteState.tick_flags options remaining span first
  have currentGhost : current2.user.payload.ghost = false := by rw [RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost];exact settings.ghost
  have currentShallow : current2.user.payload.validation = .Shallow := by rw [RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow];exact settings.shallow
  have currentExtras : current2.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == d2.id) = some (d2.id,⟨none,#[]⟩) := by
    change current2.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) = _
    rw [fields2.2.2.2.2.2.2,fields1.2.2.2.2.2.2];exact settings.extras
  have valid0 : 0 < done.locals.size := by rw [fsz];decide
  have doneCell := Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans done0)
  obtain ⟨finalAllocation,returnStep,_,_,_⟩ := S02WildcardReturnSameStep.step options limits remaining span done current2 tracker borrowFrame
    enabled (by rw [fe];exact frameTracked) place d2 reference.tracker.global.nextPointerTag sourceChild sourceChild (some reference.tracker.global.nextPointerTag) reference.offset len sourceNode
    sourceTaggedAfter sourcePresentAfter sourceHidden sourcePositiveAfter sourceActivity destination.tracker.global.nextPointerTag child returnNode taggedAfter returnPresentAfter returnSame parentless leaf returnHidden
    ownedTags hiddenFrame runtimeAfter returnPositiveAfter distinctAfter orderAfter (by change GeneralBorrowFreshRootSupportCutoff.ExposedBound updated.extra _;rw [extra];exact exposed)
    (by change ∀ valid : 0<updated.extra.roots.size,updated.extra.roots[0]≠child;rw [extra];exact notPrimary) shortAfter
    (by
      change (reference.offset+len).toNat≤destination.offset.toNat ∨ (destination.offset+1).toNat≤reference.offset.toNat
      rw [destOffset,stopEq]
      rcases separation with left | right
      · exact Or.inl left
      · exact Or.inr (Nat.le_trans (by simp only [UInt64.toNat_add]; exact Nat.mod_le _ _) right))
    afterActivity settings.thread settings.active settings.race
    (by rw [fields2.2.2.2.2.2.1,fields1.2.2.2.2.2.1];exact settings.backend) currentGhost currentShallow #[] currentExtras (by simp)
    true settings.fuel settings.debugOff settings.validationFuel (fb.trans body) doneLocation valid0 (by rw [doneCell]) (by rw [doneCell])
    (by rw [fe];exact noClocks) (by rw [frp];exact returnPlace) (frc.trans continuation) allDone (fva.trans varargs)
    (flags2.1.trans (flags1.1.trans settings.unchecked)) (flags2.2.trans (flags1.2.trans settings.noGc)) settings.fixed
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span done current2
  let sourceReleased := (d2.entry.allocation.extra.releaseProtector reference.tracker.global.nextPointerTag tracker.global.protectedTags).tree
  let priorMemory := StackPopRelease.commitTree accounted.memory d2.id d2.entry sourceReleased
  let released := (sourceReleased.releaseProtector destination.tracker.global.nextPointerTag tracker.global.protectedTags).tree
  let afterPop := S04FinalReturnVariantsInput.afterPop #[] done accounted tracker borrowFrame priorMemory d2.id d2.entry released (settings.thread.topUserRelevantFrame.getD 0)
  let finished := CanonicalCopy.replaceAllocation afterPop d2.id d2.entry.kind finalAllocation
  have last : ExecutionMachine.step (config options (remaining+1) span) limits () (Storage.withCurrent #[] done current2) = (finished,.ok true) := returnStep
  have trace := SuccessfulTrace.append bodyTrace (.next last (.refl _))
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨config options (remaining+1) span,limits,fun _ _ => True⟩
  have entered : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] installed after.machine) := by simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have exited : CallSafety.pastCallBoundary 1 finished := by change (0:Nat)<1;decide
  have terminal : ExecutionMachine.step (config options (remaining+1) span) limits () finished = (finished,.ok false) := rfl
  exact ⟨Storage.withCurrent #[] installed after.machine,finished,actual,trace,terminal,rfl,
    SuccessfulTrace.no_errors safety 1 _ finished entered trace exited,SuccessfulTrace.no_ub safety 1 _ finished entered trace exited,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩
/-- Allocation uniqueness fixes the original positive source witness. -/
theorem same_id
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len)
    (same : reference.id = input.contract.destination.id) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len 0 place := by
  obtain ⟨resolved,run⟩ := result address len input nonempty returnWildcard
  have unique := S02WildcardPositiveIdUnique.same_id address len reference resolved
  exact run (by rw [←unique];exact same)

end
end DuplicatePrefix.S02WildcardReturnSameZeroResultWildcard
#print axioms DuplicatePrefix.S02WildcardReturnSameZeroResultWildcard.result
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.S02WildcardReturnSameZeroResultWildcard.result, ``DuplicatePrefix.S02WildcardReturnSameZeroResultWildcard.same_id] do
   for dependency in (←collectAxioms declaration) do
     unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
       throwError "unapproved wildcard same count-zero Result dependency {dependency}"
