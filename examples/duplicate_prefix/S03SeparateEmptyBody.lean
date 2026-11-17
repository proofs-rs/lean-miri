import duplicate_prefix.S03EmptyPositiveBodyExact
import duplicate_prefix.S03SeparateReturnRegistration

namespace DuplicatePrefix.S03SeparateEmptyBody
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Actual positive-count live empty body with a distinct return allocation.
The argument allocation may have zero capacity: no positive argument observer
is required. The literal return entry survives both constructors and len pop;
its current concrete or wildcard capability and RuntimeFacts survive the exact
global changes. Every node/activity/order/exposure fact on that return tree is
therefore retained on the same allocation, with no future-success premise. -/
theorem to_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator) (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut=false) (implicitWrites : options.retag.implicitWrites=false)
    (debug : options.place.debugAssertions=false) (dynamicFuel validityFuel : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1) (validityEq : options.limits.validation=validityFuel+1)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (parentTag newTag : BorTag)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset count : UInt64) (nonzero : base+offset≠0) (countNonzero : count≠0)
    (input : EmptyForestSharedPool.Input entry.allocation.extra parentTag newTag)
    (size : frame.locals.size=25)
    (source1 : (frame.locals[1]'(by omega)).value=.live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm))
    (cache1 : (frame.locals[1]'(by omega)).layout=some ActualReferenceMetadata.reference)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cache2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (dead3 : (frame.locals[3]'(by omega)).value=.dead) (cache3 : (frame.locals[3]'(by omega)).layout=none)
    (dead4 : (frame.locals[4]'(by omega)).value=.dead) (dead5 : (frame.locals[5]'(by omega)).value=.dead)
    (cache4 : (frame.locals[4]'(by omega)).layout=none) (cache5 : (frame.locals[5]'(by omega)).layout=none)
    (unused : ∀id(valid:id<frame.locals.size),7≤id→id≤12→(frame.locals[id]'valid)=⟨.dead,none⟩)
    (body : frame.body=RootBody.reflected.body.body) (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance) (location : frame.location=.mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace=none) (all : CopyHelperCleanup.AllImmediate frame)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker) (mode : tracker.retagMode=.Default)
    (nextTag : tracker.global.nextPointerTag = newTag)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval=0)
    (fixed : machine.threads.fixedScheduling=true)
    (metadata : machine.user.payload.payload.user.types.metadata=PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4)=false)
    (borrowRuntime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (tagRoomNext : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (nodeRoomTwo : entry.allocation.extra.nodes.size+2 ≤ 4294967295)
    (race : machine.dataRace = none) (backend : machine.user.payload.payload.user.backend = .none)
    (thread : Miri.Concurrency.ThreadRecord) (activeThread : machine.threads.activeThread? = some thread)
    (topZero : thread.topUserRelevantFrame = some 0)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (cache0 : (frame.locals[0]'(by omega)).layout = none)
    (live13 : (frame.locals[13]'(by omega)).value = .live (.immediate .uninit))
    (cache13 : (frame.locals[13]'(by omega)).layout = none)
    (returnId : AllocId) (returnEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (separate : returnId ≠ id)
    (returnLive : machine.memory.live.find? (fun row => row.1 == returnId) = some (returnId,returnEntry))
    (returnRuntime : DuplicatePrefixBorrowContract.RuntimeFacts returnEntry.allocation.extra tracker.global)
    (returnSource returnSelected : Option UniIndex) (returnMaximum : Option BorTag) (returnOffset returnLen : UInt64)
    (returnPositive : DuplicatePrefixBorrowAuthorization.Positive returnEntry.allocation.extra tracker.global.protectedTags
      returnSource returnSelected returnMaximum returnOffset returnLen) :
    ∃ result : CompilerFrameContext.ActualFrame,
      ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      ∃ finalTree : BorrowTree, ∃ finalTracker : MachineHooks.BorrowState,
      finalTree = (S03EmptyNextLenInput.form entry.allocation.extra tracker.global borrowRuntime parentTag
        (nextTag.symm ▸ input) fresh nodeRoomTwo).after ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result finalMachine) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧ result.locals.size = 25 ∧
      result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧
      finalMachine.memory.live.find? (fun row => row.1 == id) = some (id,{entry with allocation := entry.allocation.setExtra finalTree}) ∧
      finalMachine.memory = RetagEntry.updatedMemory machine.memory id entry finalTree ∧
      finalMachine.borrowTracker = some finalTracker ∧ finalTracker.retagMode = tracker.retagMode ∧
      (∃ nextFresh : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615,
        finalTracker = PositiveLenPost.trackerAfter (ReferenceBorrowDriver.allocatedTracker tracker fresh) nextFresh id) ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      (∃ finalThread, finalMachine.threads.activeThread? = some finalThread) ∧
      finalMachine.memory.live.find? (fun row => row.1 == returnId) = some (returnId,returnEntry) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts returnEntry.allocation.extra finalTracker.global ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive returnEntry.allocation.extra finalTracker.global.protectedTags
        returnSource returnSelected returnMaximum returnOffset returnLen) := by
  obtain ⟨result,finalMachine,finalTree,finalTracker,treeEq,trace,rb,ri,rfn,re,rrp,rrc,rva,rli,rsz,rloc,r0,rAll,
      argumentLookup,memoryEq,trackedEq,modeEq,trackerEq,fg,fsh,fr,ff,fu,fnc,fa,ft,fb,fe,threadExists⟩ :=
    S03EmptyPositiveBodyExact.to_return options limits remaining span source cmp precise implicitWrites debug
      dynamicFuel validityFuel dynamicEq validityEq frame machine parentTag newTag id entry base offset count nonzero countNonzero
      input size source1 cache1 live2 cache2 dead3 cache3 dead4 dead5 cache4 cache5 unused body identity callee location noClocks all
      tracker tracked mode nextTag fresh cachedAddress present ghost shallow unchecked noGc fixed metadata notConstructed
      borrowRuntime budget dispatchFuel tagRoomNext nodeRoomTwo race backend thread activeThread topZero live0 cache0 live13 cache13
  obtain ⟨nextFresh,finalEq⟩ := trackerEq
  have kept := S03SeparateReturnRegistration.len returnEntry.allocation.extra tracker fresh nextFresh id returnRuntime
    returnSource returnSelected returnMaximum returnOffset returnLen returnPositive
  rw [←finalEq] at kept
  refine ⟨result,finalMachine,finalTree,finalTracker,treeEq,trace,rb,ri,rfn,re,rrp,rrc,rva,rli,rsz,rloc,r0,rAll,
    argumentLookup,memoryEq,trackedEq,modeEq,⟨nextFresh,finalEq⟩,fg,fsh,fr,ff,fu,fnc,fa,ft,fb,fe,threadExists,?_,kept.1,kept.2⟩
  rw [memoryEq]
  exact StackPopRelease.lookup_commit_other machine.memory id returnId entry returnEntry finalTree separate returnLive

/-- The two empty constructors retain the original argument tag and hidden
node, and preserve its release quiescence. Descendants may be added, so no
obsolete leaf claim is transported. The actual body above returns this tree. -/
theorem argument_zero (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag : BorTag) (input : EmptyForestSharedPool.Input tree parentTag global.nextPointerTag)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (room : tree.nodes.size+2 ≤ 4294967295)
    (tag : BorTag) (index : UniIndex) (node : TreeNode)
    (tagged : tree.indexOfTag tag = some index) (present : tree.nodeAt index = some node)
    (same : node.tag = tag) (hidden : node.isExposed = false)
    (quiet : S04ReturnReleaseInactive.Quiescent tree index) :
    let final := (S03EmptyNextLenInput.form tree global runtime parentTag input fresh room).after
    final.indexOfTag tag = some index ∧
    (∃ current, final.nodeAt index = some current ∧ current.tag = tag ∧ current.isExposed = false) ∧
    S04ReturnReleaseInactive.Quiescent final index := by
  let second := S03EmptyNextLenInput.form tree global runtime parentTag input fresh room
  have firstTagged := S03EmptySharedFrame.tagged input tag index tagged
  have finalTagged := S03EmptySharedFrame.tagged second tag index firstTagged
  obtain ⟨middle,middlePresent,middleTag,_,middleHidden⟩ := S03EmptySharedFrame.old_node input index node present
  obtain ⟨current,currentPresent,currentTag,_,currentHidden⟩ := S03EmptySharedFrame.old_node second index middle middlePresent
  exact ⟨finalTagged,⟨current,currentPresent,currentTag.trans (middleTag.trans same),
    currentHidden.trans (middleHidden.trans hidden)⟩,
    S03EmptySharedFrame.quiescent second index (S03EmptySharedFrame.quiescent input index quiet)⟩

end
end DuplicatePrefix.S03SeparateEmptyBody
