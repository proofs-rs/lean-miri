import duplicate_prefix.S02WildcardReturnSameCountProtect
import duplicate_prefix.S02WildcardReturnSameCountEntry
import duplicate_prefix.S02ConcreteSourceReleasePacket
import duplicate_prefix.S02FnEntryFreshNode
import duplicate_prefix.S02SameDestinationLiveTransport
import duplicate_prefix.S02ConcreteCallPreamble
import duplicate_prefix.S02PositiveFinishFrame
import duplicate_prefix.RootEntryFinish
namespace DuplicatePrefix.S02WildcardReturnSameCountInitial
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Actual arbitrary-count entry for concrete source and same-allocation wildcard
return, retaining the source and parentless return owner on the same post-state. -/
theorem enters
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615),
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker firstFresh reference.id reference.entry tag reference.offset len
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
      let args := (RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted ({} : FrameState) reference.id reference.tracker.global.nextPointerTag) count).frame
      let changed := {args with location := .unwinding ⟨601⟩}
      let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
      ∃ (destination : DuplicatePrefixReturnPlaceInput.Input current place)
        (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
        (raw : GeneralBorrowRawFnEntry.Input reference.entry.allocation.extra reference.tracker.global)
        (query : UniIndex) (node : TreeNode)
        (post : S02WildcardReturnSameCountEntry.Packet options (remaining+1) span limits.retag current place destination #[] changed owned secondFresh
          reference.tracker.global.nextPointerTag query raw.selected raw.maximum reference.offset len node),
        raw.parentTag = tag ∧ raw.offset = reference.offset ∧ raw.len = len ∧
        node.tag = reference.tracker.global.nextPointerTag ∧ node.children = #[] ∧ node.isExposed = false ∧
        destination.id = reference.id ∧ destination.offset = input.contract.destination.offset ∧
        Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
          RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
          #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),.Copy (EmptyRootArguments.second count)]
          false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[]
            (PositiveRootInstalledFrame.installed root adjusted count {} reference.id reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag)
            (S04ProtectUninit.finished current place destination #[] changed owned secondFresh post.tree post.updated).machine) ∧
        post.updated.extra.locations.size = post.updated.byteSize ∧ post.updated.extra.nodes.size+8 < 65536 ∧
        (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
          destination.tracker.global.nextPointerTag).global.nextPointerTag.value.toNat+7 < 18446744073709551615 := by
  obtain ⟨reference,firstFresh,argument,destination,secondFresh,_tree,_updated,sameId,destOffset,destEntry,_⟩ :=
    S02WildcardReturnSameCountProtect.after_argument id tag address len count input nonempty sameAllocation returnWildcard
  let machine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawFnEntryScope.resultMachine machine reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let args := RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted ({} : FrameState) reference.id reference.tracker.global.nextPointerTag) count
  let changed := {args.frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  have binding := reference.binding
  simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
  have destId : destination.id = input.contract.destination.id := sameId.trans (binding.1.symm.trans sameAllocation)
  have wildcard : destination.pointer.provenance = .wildcard := by
    have physical := congrArg (fun p : Pointer (Option Provenance) => p.provenance)
      (destination.physicalPointer.symm.trans input.contract.destination.physicalPointer)
    simp only [Pointer.withOptionalProvenance] at physical
    rw [Option.some.inj physical];exact returnWildcard
  have frameBorrow : changed.extra.borrowTracker = some owned := by
    simp only [changed,args,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,RootFrameData.cache,
      RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,owned]
  have extras : current.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    change machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _
    rw [(RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2,destId];exact input.return_extras
  obtain ⟨runtime,roots,initialOrder,headroom,_fresh⟩ := S02SameDestinationReady.local_facts_after_argument input reference firstFresh destination destEntry
  have model := S02SeparateDestinationReady.model_after_argument input reference firstFresh
  obtain ⟨_same,sourceRaw,sourceParent,sourceOffset,sourceLength,_source,_selected,_maximum,runtimeInitial⟩ :=
    S05ConcreteEntryBridge.from_positive id tag address len reference input.contract.runtime input.contract.resources
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have sourceRoom : reference.entry.allocation.extra.nodes.size+1 < 65536 := by
    have room := input.contract.resources.nodeRoom (reference.id,reference.entry) member
    dsimp only at room;omega
  obtain ⟨sourceChild,sourceNode,sourceTagged,sourcePresent,sourceSame,sourceHidden,sourceRuntime,⟨sourcePositive⟩,
    sourceActive,sourceRoots,sourceOrder,sourceShort⟩ := S02ConcreteSourceReleasePacket.release_ready
    reference.entry.allocation.extra reference.tracker ({} : FrameState) reference.id runtimeInitial sourceRaw sourceRoom
  obtain ⟨metadataChild,metadataNode,metadataTagged,metadataPresent,_metadataTag,_metadataParent,sourceLeaf,_metadataHidden⟩ :=
    S02FnEntryFreshNode.node reference.entry.allocation.extra reference.tracker ({} : FrameState) reference.id runtimeInitial sourceRaw
  have childEq : metadataChild = sourceChild := Option.some.inj (metadataTagged.symm.trans sourceTagged)
  subst metadataChild
  have nodeEq : metadataNode = sourceNode := Option.some.inj (metadataPresent.symm.trans sourcePresent)
  subst metadataNode
  simp only [sourceParent,sourceOffset,sourceLength] at sourceTagged sourcePresent sourcePositive sourceActive sourceLeaf
  have trackerEq : destination.tracker = ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,reference.tracker.retagMode⟩ :=
    Option.some.inj destination.enabled.symm
  have beforeTagged : destination.entry.allocation.extra.indexOfTag reference.tracker.global.nextPointerTag = some sourceChild := by rw [destEntry];exact sourceTagged
  have beforePresent : destination.entry.allocation.extra.nodeAt sourceChild = some sourceNode := by rw [destEntry];exact sourcePresent
  have beforeActive : GeneralBorrowFreshActiveWithin.ActiveWithin destination.entry.allocation.extra sourceChild .Write reference.offset (reference.offset+len) := by rw [destEntry];exact sourceActive
  have beforePositive : DuplicatePrefixBorrowAuthorization.Positive destination.entry.allocation.extra destination.tracker.global.protectedTags
      (some sourceChild) (some sourceRaw.selected) sourceRaw.maximum reference.offset len := by rw [destEntry,trackerEq];exact sourcePositive
  have separation := S02SameDestinationLiveTransport.actual_reference_disjoint id tag address len input nonempty sameAllocation reference
  have stopEq : (reference.offset+len).toNat = reference.offset.toNat+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt];exact Nat.lt_of_le_of_lt reference.borrow.bounds reference.entry.allocation.extra.locations.size.bytes.toNat_lt
  have disjoint : destination.offset.toNat+1 ≤ reference.offset.toNat ∨ (reference.offset+len).toNat ≤ destination.offset.toNat := by rw [destOffset,stopEq];exact separation.symm
  obtain ⟨post⟩ := S02WildcardReturnSameCountEntry.after_current limits.retag current model place destination runtime roots initialOrder headroom secondFresh wildcard
    #[] changed owned frameBorrow #[] extras (by simp) reference.tracker.global.nextPointerTag sourceChild sourceRaw.selected sourceRaw.maximum
    reference.offset len sourceNode beforeTagged beforePresent sourceLeaf sourceHidden disjoint beforePositive beforeActive
  let tree := post.tree
  let updated := post.updated
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  have finishShape := S02PositiveFinishFrame.after_destination_registration root (RawRootInvocation.locals before place input.contract.model.noDataRace)
    adjusted count reference.id destination.id reference.tracker.global.nextPointerTag destination.tracker.global.nextPointerTag
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
    rw [post.protect]
    exact finish
  obtain ⟨prefixState,preambleArg,preambleContinue⟩ := S02ConcreteCallPreamble.prefix_and_continuation id tag address len count input nonempty
  have sameAfter : prefixState = Storage.withCurrent #[] args.frame current := (EStateM.Result.ok.inj (preambleArg.symm.trans argument)).2
  have actual := preambleContinue _ (sameAfter ▸ tail)
  have initialGrowth := GeneralBorrowRawFnEntryResources.resources reference.entry.allocation.extra reference.tracker ({} : FrameState) reference.id runtimeInitial sourceRaw
  have firstGrowth := initialGrowth.2.2.1
  simp only [sourceParent,sourceOffset,sourceLength] at firstGrowth
  have currentGrowth : destination.entry.allocation.extra.nodes.size ≤ reference.entry.allocation.extra.nodes.size+1 := by rw [destEntry];exact firstGrowth
  have reserve := input.contract.resources.nodeRoom (reference.id,reference.entry) member
  change reference.entry.allocation.extra.nodes.size+16 < 65536 at reserve
  have postGrowth := post.growth
  have refTracker : reference.tracker = input.contract.tracker := Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
  have tagReserve : reference.tracker.global.nextPointerTag.value.toNat+16 < 2^64 := by rw [refTracker];exact input.contract.resources.tagRoom
  have firstSuccessor := GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag firstFresh
  have secondSuccessor := GenericFunctionEntryNumerics.successor_value destination.tracker.global.nextPointerTag secondFresh
  refine ⟨reference,firstFresh,destination,secondFresh,sourceRaw,sourceChild,sourceNode,post,sourceParent,sourceOffset,sourceLength,
    sourceSame,sourceLeaf,sourceHidden,sameId,destOffset,actual,?_,by omega,?_⟩
  · have borrowSize := post.physical.borrowSize
    have bytes := post.physical.size
    rw [post.physicalEntry] at borrowSize bytes
    change post.updated.extra.locations.size.bytes = post.physical.capacity at borrowSize
    change post.updated.byteSize = Size.ofBytes post.physical.capacity at bytes
    change Size.ofBytes post.updated.extra.locations.size.bytes = post.updated.byteSize
    rw [borrowSize]
    exact bytes.symm
  · change (TypedRetagEmpty.successorTag destination.tracker.global.nextPointerTag secondFresh).value.toNat+7 < 18446744073709551615
    have currentCounter : destination.tracker.global.nextPointerTag.value.toNat = reference.tracker.global.nextPointerTag.value.toNat+1 := by rw [trackerEq];exact firstSuccessor
    omega
end
end DuplicatePrefix.S02WildcardReturnSameCountInitial
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardReturnSameCountInitial.enters) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved concrete source wildcard count entry dependency {dependency}"
