import duplicate_prefix.S03IntegerZeroInitTail
import duplicate_prefix.S03SeparateEmptyArgument
import duplicate_prefix.ConcreteEmptyRootArgumentProperties

namespace DuplicatePrefix.S03SeparateLiveInit
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CanonicalConfigFacts ActualReferenceContext DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Actual initStackFrame for a live concrete empty argument in the SAME
allocation distinct from a concrete return place. The allocator Input, current destination
Input and release packet are all derived from initial data. Count is arbitrary. -/
theorem enters
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (limits : ExecutionMachine.Limits) (before : Before)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra original.tracker.global)
    (distinct : original.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder original.entry.allocation.extra)
    (headroom : original.entry.allocation.extra.nodes.size+1 < 65536)
    (first : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (S03LiveEmptyState.next original.tracker first).global.nextPointerTag.value < 18446744073709551615)
    (argumentId : AllocId) (argumentEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (argumentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts argumentEntry.allocation.extra original.tracker.global)
    (argumentLive : before.memory.live.find? (fun row => row.1 == argumentId) = some (argumentId,argumentEntry))
    (argumentBase : UInt64)
    (argumentCached : before.user.addresses.baseAddr.find? (fun row => row.allocId == argumentId) = some ⟨argumentId,argumentBase⟩)
    (argumentRoom : argumentEntry.allocation.extra.nodes.size+1 ≤ 4294967295)
    (separate : original.id ≠ argumentId)
    (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : argumentEntry.allocation.extra.indexOfTag parentTag = some parent)
    (present : argumentEntry.allocation.extra.nodeAt parent = some parentNode)
    (tag : BorTag) (concrete : original.pointer.provenance = .concrete original.id tag)
    (argumentOffset count : UInt64) (nonnull : argumentBase+argumentOffset ≠ 0)
    (dynamicFuel validityFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (validityEq : options.limits.validation = validityFuel+1)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == original.id) =
      some (original.id,⟨none,#[]⟩))
    (thread : Miri.Concurrency.ThreadRecord) (active : before.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none) :
    ∃ (slot : ConcreteEmptyPoolEntry.Input argumentEntry.allocation.extra parentTag original.tracker.global.nextPointerTag) (updated : Allocation Provenance BorrowTree),
    let raw := RawRootInvocation.root before place model.noDataRace
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete argumentId original.tracker.global.nextPointerTag) (Size.ofBytes (argumentBase+argumentOffset))) 0 ActualReferenceMetadata.reference).imm
    let args := RootArgumentsTwo.result (ConcreteEmptyRootArguments.firstDone raw adjusted {} argumentId original.tracker.global.nextPointerTag) count
    let current := S03SeparateEmptyArgument.argumentsMachine original first argumentId argumentEntry parentTag slot
    let input := S03SeparateEmptyArgument.after_raw_input original runtime first argumentId argumentEntry parentTag slot separate
    let owned := ({} : FrameState).addProtector argumentId original.tracker.global.nextPointerTag
    let tree := GeneralBorrowRawFnEntryArgument.finalTree original.entry.allocation.extra (S03LiveEmptyState.next original.tracker first) tag original.offset 1
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker (S03LiveEmptyState.next original.tracker first) second)
      (S03LiveEmptyState.next original.tracker first).global.nextPointerTag
    let written := (tree.performBorrowAccessRange (.concrete (S03LiveEmptyState.next original.tracker first).global.nextPointerTag)
      (Size.ofBytes original.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    let after := Storage.withCurrent #[]
      (CallEntryFacts.doneRootFrame {TypedBorrowSteps.registeredFrame
        {args.frame with location := .unwinding ⟨601⟩} owned original.id
          (S03LiveEmptyState.next original.tracker first).global.nextPointerTag with location := .unwinding ⟨559⟩})
      (S04ProtectUninit.finished current place input #[] {args.frame with location := .unwinding ⟨601⟩}
        owned second tree updated).machine
    Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete argumentId parentTag) (Size.ofBytes (argumentBase+argumentOffset))) 0 ActualReferenceMetadata.reference).imm,
        ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
      ⟨⟨#[]⟩,before⟩ = .ok () after ∧
    updated.extra = written ∧ updated.byteSize = original.entry.allocation.byteSize ∧
    updated.len = original.entry.allocation.len ∧ updated.mutability = .Mut ∧
    InitMaskCopy.WellFormed updated.initializationMask ∧
    updated.initializationMask.len = original.entry.allocation.initializationMask.len ∧
    (∀ row ∈ updated.provenanceMap.ptrs, row.1.bytes.toNat+8≤updated.len) ∧
    DuplicatePrefixBorrowContract.RuntimeFacts written global ∧
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder written ∧
    ∃ child, written.indexOfTag (S03LiveEmptyState.next original.tracker first).global.nextPointerTag = some child ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive written global.protectedTags (some child)
        original.selectedRoot original.maximum original.offset 1) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin written child .Write original.offset (original.offset+1) := by
  let slot := ConcreteEmptyRuntimeEntry.form argumentEntry.allocation.extra original.tracker.global.protectedTags parentTag
    original.tracker.global.nextPointerTag argumentRuntime.formed parent parentNode tagged present
    (ConcreteEmptyRuntimeEntry.counter_fresh _ _ argumentRuntime.below) argumentRoom
  have currentRuntime := (S03SeparateEmptyArgument.facts original runtime first argumentId).1
  let raw := RawRootInvocation.root before place model.noDataRace
  let rawMachine := RawRootInvocation.machine #[] before
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete argumentId original.tracker.global.nextPointerTag) (Size.ofBytes (argumentBase+argumentOffset))) 0 ActualReferenceMetadata.reference).imm
  let args := RootArgumentsTwo.result (ConcreteEmptyRootArguments.firstDone raw adjusted {} argumentId original.tracker.global.nextPointerTag) count
  let current := S03SeparateEmptyArgument.argumentsMachine original first argumentId argumentEntry parentTag slot
  let input := S03SeparateEmptyArgument.after_raw_input original runtime first argumentId argumentEntry parentTag slot separate
  let owned := ({} : FrameState).addProtector argumentId original.tracker.global.nextPointerTag
  have initialSlot (i : Fin 25) : (raw.frame.locals[i.val]'(raw.valid i)) = ⟨.dead,none⟩ := by
    have rows := congrArg (fun rows : Array (LocalState Provenance LocalLayout) => rows[i.val]?)
      (RawRootInvocation.locals before place model.noDataRace)
    have row : raw.frame.locals[i.val]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simpa only [Array.getElem?_replicate,i.isLt,↓reduceIte] using rows
    exact Option.some.inj ((Array.getElem?_eq_getElem (raw.valid i)).symm.trans row)
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span model.preciseOff model.implicitOff
  have arguments := ConcretePoolRootArgumentScope.scope options limits remaining span ctx model.debugOff model.nullComparator
    dynamicFuel validityFuel dynamicEq validityEq argumentId parentTag original.tracker argumentBase argumentOffset count nonnull
    argumentEntry #[] raw rawMachine (congrArg (fun row => row.value) (initialSlot EmptyRootArguments.i1))
    (congrArg (fun row => row.layout) (initialSlot EmptyRootArguments.i1)) (congrArg (fun row => row.value) (initialSlot EmptyRootArguments.i2))
    (congrArg (fun row => row.layout) (initialSlot EmptyRootArguments.i2)) model.ghostOff model.shallow argumentCached argumentLive
    {} (RawRootInvocation.frame_borrow before place model.noDataRace original.tracker original.enabled)
    original.enabled first slot model.metadata notConstructed
  have frameBorrow : args.frame.extra.borrowTracker = some owned := by
    simp only [args,RootArgumentsTwo.result,ConcreteEmptyRootArguments.firstDone,ConcreteEmptyRootArguments.protectedRoot,
      RootFrameData.write,RootFrameData.live,RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,owned]
  have dead (i : Fin 25) (ne1 : i.val ≠ 1) (ne2 : i.val ≠ 2) : (args.frame.locals[i.val]'(args.valid i)).value = .dead := by
    rw [ConcreteEmptyRootArgumentProperties.untouched raw adjusted {} argumentId original.tracker.global.nextPointerTag count i ne1 ne2,initialSlot i]
  obtain ⟨updated,tail,properties⟩ := S03IntegerZeroInitTail.run limits current
    (S03SeparateEmptyArgument.model original model first argumentId argumentEntry parentTag slot) place input currentRuntime
    distinct order headroom second tag concrete #[] args.frame owned frameBorrow #[] extras (by simp)
    args.body args.size (dead ⟨0,by decide⟩ (by decide) (by decide)) (dead ⟨6,by decide⟩ (by decide) (by decide))
    (dead ⟨13,by decide⟩ (by decide) (by decide)) (dead ⟨14,by decide⟩ (by decide) (by decide))
    args.noClocks args.identity args.callee
  have push := CallEntryFacts.actual_call_hooks_push_raw options () (remaining+1) span limits model.debugOff
    (⟨⟨#[]⟩,before⟩ : RootState) (.memory place) thread active noCache
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span #[] raw.frame rawMachine
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span #[] raw.frame raw.frame rawMachine
  have control := RawRootInvocation.control before place model.noDataRace
  have preamble : raw.frame.location = .unwinding ⟨559⟩ := control.1
  have unchanged : {raw.frame with trackCallerArg := none} = raw.frame := by rw [←control.2.1]
  simp only [preamble] at unchanged
  refine ⟨slot,updated,?_,properties⟩
  rw [RootCallCore.actual_entry_eq]
  unfold RootCallCore.core
  simp only [bind,EStateM.bind]
  unfold CallEntryFacts.config at push
  rw [push,RawRootInvocation.raw_eq #[] before place model.noDataRace]
  simp only [EStateM.bind]
  rw [getFrame]
  simp only [EStateM.bind,preamble,pure,EStateM.pure]
  rw [unchanged,setFrame]
  simp only [EStateM.bind]
  rw [arguments]
  simp only [EStateM.bind]
  exact tail

end
end DuplicatePrefix.S03SeparateLiveInit
