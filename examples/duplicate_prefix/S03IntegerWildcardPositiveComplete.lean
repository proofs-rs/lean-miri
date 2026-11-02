import duplicate_prefix.S03IntegerZeroFrame
import duplicate_prefix.S03IntegerWildcardInit
import duplicate_prefix.S03ReturnWildcardMetadata
import duplicate_prefix.S03EmptyIntegerReturnWildcard
import duplicate_prefix.SuccessfulTraceTerminal

namespace DuplicatePrefix.S03IntegerWildcardPositiveComplete
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Actual initial NoProv positive-count call with a wildcard destination through its body and original Return.
Every post-init permission and physical field below is derived from the call's
actual protection/uninit result; no future Input or operation success is a premise. -/
theorem complete
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (limits : ExecutionMachine.Limits) (before : Before)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (first : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag.value < 18446744073709551615)
    (wildcard : input.pointer.provenance = .wildcard)
    (address count : UInt64) (nonzero : address ≠ 0) (countNonzero : count ≠ 0)
    (dynamicFuel validityFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validityEq : options.limits.validation = validityFuel+1)
    (bodyFresh : (RootZeroInvocationState.held input.tracker first second).global.nextPointerTag.value < 18446744073709551615)
    (bodyRoomNext : (RootZeroInvocationState.held input.tracker first second).global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (budget : Nat) (dispatchEq : limits.callDispatch = budget+1)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,#[]⟩))
    (thread : Miri.Concurrency.ThreadRecord) (active : before.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before (.integer address) 0 count place := by
  obtain ⟨tree,updated,entry,treeEq,byteSize,bytes,mutable,maskValid,maskLength,pointerBounds,capacity,
    postRuntime,postShort,postDistinct,postOrder,postExposed,child,childTagged,roots,⟨childPositive⟩,activity,
    node,returnPresent,returnSame,parentless,leaf,returnHidden⟩ := S03IntegerWildcardInit.enters limits before model
      place input runtime distinct order headroom first second wildcard address count nonzero dynamicFuel validityFuel dynamicEq validityEq
      notConstructed extras thread active noCache
  let start := S03IntegerWildcardInit.installed input model.noDataRace address count first second tree updated
  let frame := S03IntegerZeroFrame.installed (RawRootInvocation.root before place model.noDataRace)
    address count {} input.id (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag
  let tracker := RootZeroInvocationState.held input.tracker first second
  let borrowFrame : FrameState := ({} : FrameState).addProtector input.id
    (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag
  let currentInput := S03IntegerZeroState.input input first
  let args := EmptyRootArguments.result (RawRootInvocation.root before place model.noDataRace) address count
  let destination := S03ReturnWildcardMetadata.of_protection currentInput wildcard #[]
    {args.frame with location := .unwinding ⟨601⟩} {} second tree updated
    (S03IntegerWildcardInit.written input first second tree) treeEq byteSize bytes mutable maskValid maskLength pointerBounds capacity
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
  have hiddenFrame : S04ReturnReleaseParent.HiddenFrame updated.extra borrowFrame := by
    intro row member query value found sameTag
    have rowEq : row = (input.id,(ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag) := by
      simpa only [borrowFrame,FrameState.addProtector,Array.toList_push,Array.toList_empty,List.nil_append,List.mem_singleton] using member
    subst row
    rw [treeEq] at found
    have mapped := postRuntime.formed.allocator.nodeTags query value found
    rw [sameTag] at mapped
    have equal : query = child := Option.some.inj (mapped.symm.trans childTagged)
    subst query
    have same : value = node := Option.some.inj (found.symm.trans returnPresent)
    exact same ▸ returnHidden
  let rawFrame := RawRootInvocation.root before place model.noDataRace
  have frameMeta := S03IntegerZeroFrame.metadata rawFrame address count {} input.id
    (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag
  have frameSize := S03IntegerZeroFrame.size rawFrame address count {} input.id
    (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag
  have slots := S03IntegerZeroFrame.slot rawFrame (RawRootInvocation.locals before place model.noDataRace) address count {} input.id
    (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag
  have immediate := S03IntegerZeroFrame.immediate rawFrame (RawRootInvocation.locals before place model.noDataRace) address count {} input.id
    (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag
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
      (some child) (some child) (some (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag) input.offset 1 := by
    rw [treeEq];exact childPositive.base
  have exposedUpdated : GeneralBorrowFreshRootSupportCutoff.ExposedBound updated.extra
      (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag := by rw [treeEq];exact postExposed
  have orderUpdated : GeneralBorrowWildcardParentTagOrder.ParentTagOrder updated.extra := by rw [treeEq];exact postOrder
  have taggedUpdated : updated.extra.indexOfTag (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag = some child := by
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
  obtain ⟨done,trace,terminal,empty,noErrors,noUb⟩ := S03EmptyIntegerReturnWildcard.complete options limits remaining span frame start.machine
    tracker borrowFrame default rfl frameMeta.2.2.2.2.2.2.2.1 place destination
    (ReferenceBorrowDriver.allocatedTracker input.tracker first).global.nextPointerTag child node
    (.only rfl) taggedUpdated presentUpdated returnSame parentless leaf returnHidden hiddenFrame runtimeUpdated positiveUpdated
    geometryUpdated.1 orderUpdated exposedUpdated notPrimary geometryUpdated.2 activityUpdated
    {thread with topUserRelevantFrame := some 0} activeNow rfl model.noDataRace model.noBackend model.ghostOff model.shallow
    #[] extras (by simp) validityFuel dynamicFuel budget dynamicEq dispatchEq model.preciseOff model.implicitOff model.nullComparator
    bodyFresh bodyRoomNext model.metadata notConstructed model.debugOff validityEq (DuplicatePrefixCallModel.sourceComparator _ _ _ _ model)
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
    address count nonzero countNonzero
    (by simpa using congrArg (fun row => row.value) (slots ⟨1,by decide⟩))
    (by simpa using congrArg (fun row => row.layout) (slots ⟨1,by decide⟩)) unused
    (by simpa using congrArg (fun row => row.value) (slots ⟨13,by decide⟩))
    (by simpa using congrArg (fun row => row.layout) (slots ⟨13,by decide⟩))
    (by simpa using congrArg (fun row => row.value) (slots ⟨2,by decide⟩))
    (by simpa using congrArg (fun row => row.layout) (slots ⟨2,by decide⟩))
    (frameMeta.2.2.2.2.2.2.1.trans rawFrame.noClocks) rfl
    (frameMeta.2.2.2.1.trans (RawRootInvocation.control before place model.noDataRace).2.2.1) immediate rfl
    unchecked noGc model.fixedScheduler
  exact ⟨start,done,entry,trace,terminal,empty,noErrors,noUb,SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.S03IntegerWildcardPositiveComplete
