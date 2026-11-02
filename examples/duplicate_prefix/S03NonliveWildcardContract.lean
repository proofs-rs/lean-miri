import duplicate_prefix.S03NonliveWildcardInit
import duplicate_prefix.S03NonliveReturnWildcard
import duplicate_prefix.S03NonliveCallResources
import duplicate_prefix.S03NonliveMetadataTag
import duplicate_prefix.S03ReturnWildcardMetadata
import duplicate_prefix.S03ZeroCountBodyWildcard
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.SuccessfulTraceTerminal

namespace DuplicatePrefix.S03NonliveWildcardContract
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification S05ConsistentCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Original supported nonlive concrete empty arguments and a general wildcard
return destination, for every count. Numeric/catalog/current return metadata
are derived from the existing ConsistentContract and actual initialization;
no future state, successful suboperation or final permission is a premise. -/
theorem complete {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (contractInput : ConsistentContract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : contractInput.contract.destination.pointer.provenance = .wildcard)
    (argumentId : AllocId) (parentTag : BorTag) (argumentConcrete : pointer.provenance = .concrete argumentId parentTag)
    (argumentMetadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory argumentId (some parentTag))
    (argumentAbsent : before.memory.live.find? (fun row => row.1 == argumentId) = none)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.pointer pointer) 0 count place := by
  let facts := S03NonliveCallResources.of_contract contractInput argumentId parentTag argumentConcrete
  let input := contractInput.contract.destination
  let model := contractInput.contract.model
  let runtime := facts.runtime
  let distinct := facts.distinct
  let order := facts.order
  let headroom := facts.headroom
  let first := facts.first
  let second := facts.second
  let base := facts.base
  let offset := facts.offset
  let notConstructed := contractInput.slice_not_constructed
  let extras := contractInput.return_extras
  let thread := contractInput.contract.thread
  let active := contractInput.contract.active
  change input.pointer.provenance = .wildcard at wildcard
  have metadataNone := S03NonliveMetadataTag.changeTag before.memory argumentId (some parentTag) none argumentMetadata argumentAbsent
  obtain ⟨tree,updated,entry,treeEq,byteSize,bytes,mutable,maskValid,maskLength,pointerBounds,capacity,
    postRuntime,postShort,postDistinct,postOrder,postExposed,oldMapping,child,childTagged,roots,⟨childPositive⟩,activity,
    node,returnPresent,returnSame,parentless,leaf,returnHidden⟩ := S03NonliveWildcardInit.enters limits before model
      place input runtime distinct order headroom first second wildcard argumentId parentTag base offset count facts.nonzero facts.cached
      argumentMetadata argumentAbsent facts.dynamicFuel facts.validityFuel facts.dynamicEq facts.validityEq
      notConstructed extras thread active contractInput.contract.emptyHarnessCache
  let start := S03NonliveWildcardInit.installed input runtime model.noDataRace argumentId base offset count first second tree updated
  let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal input.tracker.global first,input.tracker.retagMode⟩
  let tracker := S03NonliveCallResources.held input.tracker first second
  let argumentFrame : FrameState := ({} : FrameState).addProtector argumentId input.tracker.global.nextPointerTag
  let borrowFrame := argumentFrame.addProtector input.id next.global.nextPointerTag
  let adjusted := (RetagReferencePlace.sliceValue PreparedReflection.actual.runtime.target.base
    (Pointer.new (.concrete argumentId input.tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))
      0 ActualReferenceMetadata.reference).imm
  let rawFrame := RawRootInvocation.root before place model.noDataRace
  let frame := PositiveRootInstalledFrame.installed rawFrame adjusted count {} argumentId input.tracker.global.nextPointerTag
    input.id next.global.nextPointerTag
  let currentInput := S03NonliveZeroState.input input first argumentId runtime
  let args := RootArgumentsTwo.result (ConcreteEmptyRootArguments.firstDone rawFrame adjusted {} argumentId input.tracker.global.nextPointerTag) count
  let destination := S03ReturnWildcardMetadata.of_protection currentInput wildcard #[]
    {args.frame with location := .unwinding ⟨601⟩} argumentFrame second tree updated
    (S03NonliveWildcardInit.written input first second tree) treeEq byteSize bytes mutable maskValid maskLength pointerBounds capacity
  have initialPositive := input.borrow
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,wildcard] at binding
  have source := binding.1
  rw [source] at initialPositive
  have oldNonempty := initialPositive.wildcardRoot rfl
  have notPrimary : ∀ valid : 0 < updated.extra.roots.size, updated.extra.roots[0] ≠ child := by
    rw [treeEq]
    intro valid same
    have rootAt : input.entry.allocation.extra.roots[0]'oldNonempty = child := by
      simpa only [roots,Array.getElem_push_lt oldNonempty] using same
    have member : child ∈ input.entry.allocation.extra.roots.toList := by
      rw [←rootAt]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem oldNonempty)
    have nodup := postDistinct
    rw [roots,Array.toList_push,List.nodup_append] at nodup
    exact nodup.2.2 child member child (by simp) rfl
  have firstFresh : GeneralBorrowTagMap.Fresh input.entry.allocation.extra.tagMapping input.tracker.global.nextPointerTag :=
    (GeneralBorrowWildcardFnEntryRegistration.prepare input.entry.allocation.extra input.tracker.global {} argumentId first runtime
      input.source input.selectedRoot input.maximum input.offset 1 input.borrow).2.2.2.2.2
  have firstMissing : input.entry.allocation.extra.indexOfTag input.tracker.global.nextPointerTag = none := by
    unfold BorrowTree.indexOfTag UniKeyMap.get
    rw [GeneralBorrowTagMap.fresh_find _ _ firstFresh]
    rfl
  have tagDifferent : next.global.nextPointerTag ≠ input.tracker.global.nextPointerTag := by
    intro equal
    have same := congrArg (fun t : BorTag => t.value.toNat) equal
    have successor := GenericFunctionEntryNumerics.successor_value input.tracker.global.nextPointerTag first
    change (TypedRetagEmpty.successorTag input.tracker.global.nextPointerTag first).value.toNat = _ at same
    omega
  have missingWritten := oldMapping input.tracker.global.nextPointerTag tagDifferent
  have hiddenFrame : S04ReturnReleaseParent.HiddenFrame updated.extra borrowFrame := by
    intro row member query value found sameTag
    have cases : row = (argumentId,input.tracker.global.nextPointerTag) ∨ row = (input.id,next.global.nextPointerTag) := by
      simpa only [borrowFrame,argumentFrame,FrameState.addProtector,Array.toList_push,Array.toList_empty,
        List.nil_append,List.mem_cons,List.mem_singleton,List.mem_append,List.not_mem_nil,or_false,next] using member
    rcases cases with rfl | rfl
    · rw [treeEq] at found
      have mapped := postRuntime.formed.allocator.nodeTags query value found
      rw [sameTag] at mapped
      change (S03NonliveWildcardInit.written input first second tree).indexOfTag input.tracker.global.nextPointerTag = some query at mapped
      rw [missingWritten,firstMissing] at mapped
      cases mapped
    · rw [treeEq] at found
      have mapped := postRuntime.formed.allocator.nodeTags query value found
      rw [sameTag] at mapped
      have equal : query = child := Option.some.inj (mapped.symm.trans childTagged)
      subst query
      have same : value = node := Option.some.inj (found.symm.trans returnPresent)
      exact same ▸ returnHidden
  have frameMeta := PositiveRootInstalledFrame.metadata rawFrame adjusted count {} argumentId input.tracker.global.nextPointerTag
    input.id next.global.nextPointerTag
  have frameSize := PositiveRootInstalledFrame.size rawFrame adjusted count {} argumentId input.tracker.global.nextPointerTag
    input.id next.global.nextPointerTag
  have slots := PositiveRootInstalledFrame.slot rawFrame (RawRootInvocation.locals before place model.noDataRace) adjusted count {}
    argumentId input.tracker.global.nextPointerTag input.id next.global.nextPointerTag
  have immediate := PositiveRootInstalledFrame.immediate rawFrame (RawRootInvocation.locals before place model.noDataRace) adjusted count {}
    argumentId input.tracker.global.nextPointerTag input.id next.global.nextPointerTag
  obtain ⟨oldTracker,oldEnabled,defaultMode⟩ := model.defaultTracker
  have sameTracker : oldTracker = input.tracker := Option.some.inj (oldEnabled.symm.trans input.enabled)
  subst oldTracker
  have default : tracker.retagMode = .Default := defaultMode
  have activeNow : start.machine.threads.activeThread? = some {thread with topUserRelevantFrame := some 0} :=
    PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 thread 0 active
  have controls := RootZeroInvocationState.raw_control options remaining span before
  have unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl start.machine.user).checkedArithmetic = false := by
    change ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl (RawRootInvocation.machine #[] before).user).checkedArithmetic = false
    rw [controls];exact model.unchecked
  have noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl start.machine.user).gcInterval = 0 := by
    change ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl (RawRootInvocation.machine #[] before).user).gcInterval = 0
    rw [controls];exact model.noGc
  have geometryUpdated : updated.extra.roots.toList.Nodup ∧ updated.extra.nodes.size < 65536 := by
    rw [treeEq];exact ⟨postDistinct,postShort⟩
  have runtimeUpdated : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra tracker.global := by rw [treeEq];exact postRuntime
  have positiveUpdated : DuplicatePrefixBorrowAuthorization.Positive updated.extra tracker.global.protectedTags
      (some child) (some child) (some (next).global.nextPointerTag) input.offset 1 := by
    rw [treeEq];exact childPositive.base
  have exposedUpdated : GeneralBorrowFreshRootSupportCutoff.ExposedBound updated.extra
      (next).global.nextPointerTag := by rw [treeEq];exact postExposed
  have orderUpdated : GeneralBorrowWildcardParentTagOrder.ParentTagOrder updated.extra := by rw [treeEq];exact postOrder
  have taggedUpdated : updated.extra.indexOfTag (next).global.nextPointerTag = some child := by
    rw [treeEq];exact childTagged
  have presentUpdated : updated.extra.nodeAt child = some node := by rw [treeEq];exact returnPresent
  have activityUpdated : GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra child .Write input.offset (input.offset+1) := by
    rw [treeEq];exact activity
  have unused : ∀ index (valid : index < frame.locals.size), 7 ≤ index → index ≤ 12 → frame.locals[index] = ⟨.dead,none⟩ := by
    intro index valid lower upper
    have bound : index < 25 := by omega
    have actual := slots ⟨index,bound⟩
    simpa only [show ¬(14 = index ∨ 13 = index ∨ 6 = index ∨ 0 = index) from by omega,
      show ¬2 = index from by omega,show ¬1 = index from by omega,ite_false] using actual
  have separate := S03NonliveEmptyMetadata.separate before.memory argumentId input.id input.entry argumentAbsent input.live
  have currentMetadata : DuplicatePrefixEmptyReferenceInput.Metadata start.machine.memory argumentId none := by
    have firstMetadata := S03NonliveEmptyMetadata.replace before.memory argumentId input.id none
      {input.entry with allocation := input.entry.allocation.setExtra tree}
      metadataNone argumentAbsent separate
    have firstAbsent := S03NonliveEmptyMetadata.live_replace_absent before.memory argumentId input.id
      {input.entry with allocation := input.entry.allocation.setExtra tree} argumentAbsent separate
    exact S03NonliveEmptyMetadata.replace _ argumentId input.id none {input.entry with allocation := updated}
      firstMetadata firstAbsent separate
  have currentAbsent : start.machine.memory.live.find? (fun row => row.1 == argumentId) = none := by
    exact S03NonliveEmptyMetadata.live_replace_absent _ argumentId input.id {input.entry with allocation := updated}
      (S03NonliveEmptyMetadata.live_replace_absent before.memory argumentId input.id _ argumentAbsent separate) separate
  let argument : S04FinalReturnVariantsInput.ArgumentProtection start.machine.memory borrowFrame destination.id destination.entry
      next.global.nextPointerTag := .nonlive argumentId input.tracker.global.nextPointerTag currentMetadata currentAbsent rfl
  have bodyFresh : tracker.global.nextPointerTag.value < 18446744073709551615 := facts.bodyFresh
  have bodyRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615 := facts.bodyRoom
  have bodyTag : tracker.global.nextPointerTag = facts.tags 2 := facts.bodyTag
  have lenTag : (ReferenceBorrowDriver.allocatedTracker tracker bodyFresh).global.nextPointerTag = facts.tags 3 := by
    simpa only [ReferenceBorrowDriver.allocatedTracker,TypedRetagEmpty.successorTag] using facts.lenTag
  have incoming : Pointer.new (.concrete argumentId parentTag) (Size.ofBytes (base+offset)) = pointer := by
    have address := facts.address
    cases pointer with
    | mk off provenance =>
      change provenance = .concrete argumentId parentTag at argumentConcrete
      subst provenance
      cases off with
      | mk bytes => simp only [Pointer.new,Size.ofBytes] at address ⊢;rw [address]
  by_cases zero : count = 0
  · subst count
    obtain ⟨done,trace,terminal,empty,noErrors,noUb⟩ := S03ZeroCountBodyWildcard.complete options limits remaining span frame start.machine
      tracker borrowFrame default rfl frameMeta.2.2.2.2.2.2.2.1 place destination
      (next).global.nextPointerTag child node
      argument taggedUpdated presentUpdated returnSame parentless leaf returnHidden hiddenFrame runtimeUpdated positiveUpdated
      geometryUpdated.1 orderUpdated exposedUpdated notPrimary geometryUpdated.2 activityUpdated
      {thread with topUserRelevantFrame := some 0} activeNow model.noDataRace model.noBackend model.ghostOff model.shallow
      #[] extras (by simp) facts.validityFuel model.debugOff facts.validityEq (DuplicatePrefixCallModel.sourceComparator _ _ _ _ model)
      (frameMeta.1.trans rawFrame.body) (frameMeta.2.1.trans rawFrame.identity) (frameMeta.2.2.1.trans rawFrame.callee)
      frameMeta.2.2.2.2.2.2.2.2 frameSize
      (by simpa using congrArg (fun row => row.value) (slots ⟨0,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (slots ⟨0,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (slots ⟨3,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (slots ⟨4,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (slots ⟨5,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (slots ⟨4,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (slots ⟨5,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (slots ⟨2,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (slots ⟨2,by decide⟩))
      (frameMeta.2.2.2.2.2.2.1.trans rawFrame.noClocks) rfl
      (frameMeta.2.2.2.1.trans (RawRootInvocation.control before place model.noDataRace).2.2.1) immediate rfl
      unchecked noGc model.fixedScheduler
    refine ⟨start,done,?_,trace,terminal,empty,noErrors,noUb,SuccessfulTraceTerminal.prefix_step_success trace terminal⟩
    simpa only [DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue,incoming] using entry
  ·
    obtain ⟨done,trace,terminal,empty,noErrors,noUb⟩ := S03NonliveReturnWildcard.complete options limits remaining span frame start.machine
      tracker borrowFrame default rfl frameMeta.2.2.2.2.2.2.2.1 place destination
      (next).global.nextPointerTag child node
      argument taggedUpdated presentUpdated returnSame parentless leaf returnHidden hiddenFrame runtimeUpdated positiveUpdated
      geometryUpdated.1 orderUpdated exposedUpdated notPrimary geometryUpdated.2 activityUpdated
      {thread with topUserRelevantFrame := some 0} activeNow rfl model.noDataRace model.noBackend model.ghostOff model.shallow
      #[] extras (by simp) facts.validityFuel facts.dynamicFuel facts.budget facts.dynamicEq facts.dispatchEq model.preciseOff model.implicitOff model.nullComparator
      bodyFresh bodyRoom model.metadata notConstructed model.debugOff facts.validityEq (DuplicatePrefixCallModel.sourceComparator _ _ _ _ model)
      (frameMeta.1.trans rawFrame.body) (frameMeta.2.1.trans rawFrame.identity) (frameMeta.2.2.1.trans rawFrame.callee)
      frameMeta.2.2.2.2.2.2.2.2 frameSize
      (by simpa using congrArg (fun row => row.value) (slots ⟨0,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (slots ⟨0,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (slots ⟨3,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (slots ⟨4,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (slots ⟨5,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (slots ⟨4,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (slots ⟨5,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (slots ⟨3,by decide⟩))
      facts.tags facts.tagsDistinct argumentId none base offset count facts.nonzero zero currentMetadata currentAbsent facts.cached bodyTag lenTag
      (by simpa only [CanonicalConfigFacts.actual_access_runtime,facts.firstTag,Fin.val_mk,Nat.reduceEqDiff,or_false,↓reduceIte] using
        congrArg (fun row => row.value) (slots ⟨1,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (slots ⟨1,by decide⟩)) unused
      (by simpa using congrArg (fun row => row.value) (slots ⟨13,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (slots ⟨13,by decide⟩))
      (by simpa using congrArg (fun row => row.value) (slots ⟨2,by decide⟩))
      (by simpa using congrArg (fun row => row.layout) (slots ⟨2,by decide⟩))
      (frameMeta.2.2.2.2.2.2.1.trans rawFrame.noClocks) rfl
      (frameMeta.2.2.2.1.trans (RawRootInvocation.control before place model.noDataRace).2.2.1) immediate rfl
      unchecked noGc model.fixedScheduler
    refine ⟨start,done,?_,trace,terminal,empty,noErrors,noUb,SuccessfulTraceTerminal.prefix_step_success trace terminal⟩
    simpa only [DuplicatePrefixSliceArgument.first,DuplicatePrefixSliceArgument.rawValue,incoming] using entry

end
end DuplicatePrefix.S03NonliveWildcardContract
