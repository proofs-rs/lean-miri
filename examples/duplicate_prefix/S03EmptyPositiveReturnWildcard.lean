import duplicate_prefix.S04FinalReturnWildcard
import duplicate_prefix.S03EmptyPositiveBody
import duplicate_prefix.S03EmptyPositiveTreeFacts
import duplicate_prefix.S03EmptyPositiveDestination
import duplicate_prefix.S03EmptyTagState

namespace DuplicatePrefix.S03EmptyPositiveReturnWildcard
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open S04FinalReturnVariantsInput S04FinalReturnWildcardInput Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Actual positive-count live empty body and original Return rule in the SAME
allocation as its general return destination. Both zero constructors, helper
pop, caller protector release and physical return are executed.
No future return Input, execution result, or NoUB certificate is a
premise. This is the body suffix; creation of its frame and physical metadata
by the original Call.initStackFrame remains a separate connection. -/
theorem complete
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (defaultMode : tracker.retagMode = .Default)
    (enabled : machine.borrowTracker = some tracker) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (place : MPlaceTy Provenance) (destination : Destination machine place)
    (returnTag : BorTag) (child : UniIndex)
    (returnNode : TreeNode)
    (zeroTag : BorTag) (zeroIndex : UniIndex)
    (zero : S03EmptyTagState.Data destination.entry.allocation.extra zeroTag zeroIndex)
    (owned : borrowFrame.protectedTags = #[(destination.id,zeroTag),(destination.id,returnTag)])
    (differentTags : zeroTag ≠ returnTag)
    (returnTagged : destination.entry.allocation.extra.indexOfTag returnTag = some child)
    (returnPresent : destination.entry.allocation.extra.nodeAt child = some returnNode)
    (returnSame : returnNode.tag = returnTag) (parentless : returnNode.parent = none)
    (leaf : returnNode.children = #[])
    (returnHidden : returnNode.isExposed = false)
    (hiddenFrame : S04ReturnReleaseParent.HiddenFrame destination.entry.allocation.extra borrowFrame)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra tracker.global)
    (positive : DuplicatePrefixBorrowAuthorization.Positive destination.entry.allocation.extra tracker.global.protectedTags
      (some child) (some child) (some returnTag) destination.offset 1)
    (distinct : destination.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder destination.entry.allocation.extra)
    (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound destination.entry.allocation.extra returnTag)
    (notPrimary : ∀ valid : 0 < destination.entry.allocation.extra.roots.size, destination.entry.allocation.extra.roots[0] ≠ child)
    (headroom : destination.entry.allocation.extra.nodes.size+2 < 65536)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin destination.entry.allocation.extra child .Write
      destination.offset (destination.offset+1))
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (topZero : thread.topUserRelevantFrame = some 0)
    (race : machine.dataRace = none) (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) =
      some (destination.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync,
      row.1.bytes.toNat < destination.offset.toNat ∨ destination.offset.toNat + 1 ≤ row.1.bytes.toNat)
    (fuel dynamicFuel budget : Nat)
    (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (dispatchFuel : limits.callDispatch = budget+1)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (tagRoomNext : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (debugOff : options.place.debugAssertions = false)
    (validationFuel : options.limits.validation = fuel+1)
    (source : PreparedContracts.SourceComparator)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (frameSize : frame.locals.size = 25)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (dead3 : (frame.locals[3]'(by omega)).value = .dead)
    (dead4 : (frame.locals[4]'(by omega)).value = .dead)
    (dead5 : (frame.locals[5]'(by omega)).value = .dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout = none)
    (uncached5 : (frame.locals[5]'(by omega)).layout = none)
    (uncached3 : (frame.locals[3]'(by omega)).layout = none)
    (argumentOffset count : UInt64) (nonnullAddress : destination.base+argumentOffset ≠ 0) (countNonzero : count ≠ 0)
    (source1 : (frame.locals[1]'(by omega)).value = .live (.immediate
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete destination.id zeroTag) (Size.ofBytes (destination.base+argumentOffset))) 0 ActualReferenceMetadata.reference).imm))
    (cached1 : (frame.locals[1]'(by omega)).layout = some ActualReferenceMetadata.reference)
    (unused : ∀ id (valid : id < frame.locals.size), 7 ≤ id → id ≤ 12 → frame.locals[id] = ⟨.dead,none⟩)
    (live13 : (frame.locals[13]'(by omega)).value = .live (.immediate .uninit))
    (cached13 : (frame.locals[13]'(by omega)).layout = none)
    (live2 : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cached2 : (frame.locals[2]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (noLocalClocks : frame.extra.dataRace = none)
    (returnPlace : frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩)
    (continuation : frame.returnContinuation = .stop true)
    (immediateLocals : CopyHelperCleanup.AllImmediate frame)
    (varargs : frame.vaList = #[])
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
      ⟨cfg,limits,fun _ _ => True⟩
    ∃ done, SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] frame machine) done ∧
      ExecutionMachine.step cfg limits () done = (done,.ok false) ∧ done.stack.frames = #[] ∧
      CallSafety.NoErrorsBeforeReturn safety 1 (Storage.withCurrent #[] frame machine) ∧
      CallSafety.NoUBBeforeReturn safety 1 (Storage.withCurrent #[] frame machine) := by
  have quiet : S04ReturnReleaseInactive.Quiescent destination.entry.allocation.extra zeroIndex := by
    intro position valid state stored
    exact Or.inl (zero.inactive position valid state stored)
  have nodeRoomTwo : destination.entry.allocation.extra.nodes.size+2 ≤ 4294967295 := by omega
  have fits : destination.entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295 := by
    have accounting := runtime.formed.allocator.accounting
    unfold GeneralBorrowFreshStagePool.Accounting at accounting
    omega
  let sourceInput := EmptyForestSharedPool.factory destination.entry.allocation.extra zeroTag tracker.global.nextPointerTag
    zeroIndex zero.node (Classical.choice runtime.formed.depth) zero.tagged zero.present
    (GeneralBorrowParentTagInvariant.fresh _ _ runtime) runtime.formed.allocator.pool runtime.formed.allocator.accounting fits
    (DuplicatePrefixBorrowContract.vacant_clean runtime)
  obtain ⟨result,current,tree,currentTracker,treeEq,prefixTrace,fb,fi,ff,fe,frp,frc,fva,fli,fsz,resultLocation,result0,allResult,
      currentLive,currentTracked,sameMode,currentGhost,currentShallow,currentRace,currentFixed,currentUnchecked,currentNoGc,
      addressesEq,typesEq,backendEq,extrasEq,currentActive,currentRuntime,⟨currentPositive⟩,currentActivity,currentQuiet⟩ :=
    S03EmptyPositiveBody.to_return options limits remaining span source cmp precise implicitWrites debugOff dynamicFuel fuel dynamicEq validationFuel
      frame machine zeroTag tracker.global.nextPointerTag destination.id destination.entry destination.base argumentOffset count
      nonnullAddress countNonzero sourceInput frameSize source1 cached1 live2 cached2 dead3 uncached3 dead4 dead5 uncached4 uncached5 unused
      sourceBody identity callee location noLocalClocks immediateLocals tracker enabled defaultMode rfl fresh destination.cachedBase destination.live
      ghost shallow unchecked noGc fixed metadata notConstructed runtime (by omega)
      (some child) (some child) (some returnTag) destination.offset 1 positive child activity zeroIndex quiet
      budget dispatchFuel tagRoomNext nodeRoomTwo race backend thread active topZero live0 uncached0 live13 cached13
  let next := S03EmptyPositiveTreeFacts.next runtime zeroTag sourceInput fresh nodeRoomTwo
  have finalRoots : tree.roots = destination.entry.allocation.extra.roots := by
    rw [treeEq]
    exact S03EmptyPositiveTreeFacts.roots runtime zeroTag sourceInput fresh nodeRoomTwo
  have finalCapacity : tree.locations.size = destination.entry.allocation.extra.locations.size := by
    rw [treeEq]
    exact S03EmptyPositiveTreeFacts.capacity runtime zeroTag sourceInput fresh nodeRoomTwo
  have finalSize : tree.nodes.size ≤ destination.entry.allocation.extra.nodes.size+2 := by
    rw [treeEq]
    exact S03EmptyPositiveTreeFacts.size runtime zeroTag sourceInput fresh nodeRoomTwo
  have finalTagged (tag : BorTag) (index : UniIndex)
      (known : destination.entry.allocation.extra.indexOfTag tag = some index) : tree.indexOfTag tag = some index := by
    rw [treeEq]
    exact S03EmptyPositiveTreeFacts.tagged runtime zeroTag sourceInput fresh nodeRoomTwo tag index known
  have finalHiddenFrame : S04ReturnReleaseParent.HiddenFrame tree borrowFrame := by
    rw [treeEq]
    exact S03EmptyPositiveTreeFacts.hidden_frame runtime zeroTag sourceInput fresh nodeRoomTwo borrowFrame hiddenFrame
  have zeroExists : ∃ node,tree.nodeAt zeroIndex = some node ∧ node.tag = zero.node.tag ∧
      node.parent = zero.node.parent ∧ node.isExposed = zero.node.isExposed := by
    rw [treeEq]
    exact S03EmptyPositiveTreeFacts.old_node runtime zeroTag sourceInput fresh nodeRoomTwo zeroIndex zero.node zero.present
  obtain ⟨zeroNode,zeroPresent,zeroSame,zeroParent,zeroHidden⟩ := zeroExists
  have differentParent : child ≠ sourceInput.parent := by
    have parentEq : sourceInput.parent = zeroIndex := rfl
    intro same
    have indices : child = zeroIndex := same.trans parentEq
    have found := returnPresent
    rw [indices] at found
    have nodes := Option.some.inj (found.symm.trans zero.present)
    exact differentTags (zero.sameTag.symm.trans ((congrArg TreeNode.tag nodes).symm.trans returnSame))
  have returnExists : ∃ node,tree.nodeAt child = some node ∧ node.tag = returnNode.tag ∧
      node.isExposed = false ∧ node.parent = none ∧ node.children = #[] := by
    rw [treeEq]
    exact S03EmptyPositiveTreeFacts.old_leaf runtime zeroTag sourceInput fresh nodeRoomTwo child returnNode returnPresent
      differentParent returnHidden parentless leaf
  obtain ⟨returnFinal,returnFinalPresent,returnFinalTag,returnFinalHidden,returnFinalParent,returnFinalLeaf⟩ := returnExists
  let destinationCurrent := S03EmptyPositiveDestination.wildcard destination tree currentLive addressesEq finalCapacity
  have finalOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree := by
    rw [treeEq]
    exact S03EmptyPositiveTreeFacts.order runtime zeroTag sourceInput fresh nodeRoomTwo order
  have finalExposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree returnTag := by
    rw [treeEq]
    exact S03EmptyPositiveTreeFacts.exposed runtime zeroTag sourceInput fresh nodeRoomTwo returnTag exposed
  have finalNotPrimary : ∀ valid : 0 < tree.roots.size, tree.roots[0] ≠ child := by
    intro valid
    have oldValid : 0 < destination.entry.allocation.extra.roots.size := by rw [←finalRoots];exact valid
    simpa only [finalRoots] using notPrimary oldValid
  have argumentCurrent : ArgumentProtection current.memory borrowFrame destination.id
      {destination.entry with allocation := destination.entry.allocation.setExtra tree} returnTag :=
    .same zeroTag zeroIndex zeroNode owned (finalTagged zeroTag zeroIndex zero.tagged) zeroPresent (zeroHidden.trans zero.hidden) currentQuiet
  have finalDistinct : tree.roots.toList.Nodup := by rw [finalRoots];exact distinct
  have finalShort : tree.nodes.size < 65536 := by omega
  obtain ⟨currentThread,currentThreadActive⟩ := currentActive
  have valid0 : (0 : MIR.LocalId) < result.locals.size := by rw [fsz];decide
  have slot0 : result.locals[0] = ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans result0)
  have currentExtras : current.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) =
      some (destination.id,⟨none,sync⟩) := by rw [extrasEq];exact extras
  obtain ⟨updated,returned,_,_,_⟩ := S04FinalReturnWildcard.step options limits remaining span result current currentTracker borrowFrame
    currentTracked (by rw [fe];exact frameTracked) place destinationCurrent returnTag child returnFinal argumentCurrent
    (finalTagged returnTag child returnTagged) returnFinalPresent (returnFinalTag.trans returnSame)
    returnFinalParent returnFinalLeaf returnFinalHidden finalHiddenFrame
    currentRuntime currentPositive finalDistinct finalOrder finalExposed finalNotPrimary finalShort currentActivity
    currentThread currentThreadActive currentRace (backendEq.trans backend) currentGhost currentShallow sync currentExtras outside false fuel debugOff validationFuel
    (fb.trans sourceBody) resultLocation valid0 (by rw [slot0]) (by rw [slot0]) (by rw [fe];exact noLocalClocks)
    (by rw [frp];exact returnPlace) (frc.trans continuation) allResult (fva.trans varargs) currentUnchecked currentNoGc currentFixed
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span result current
  let released := (tree.releaseProtector returnTag currentTracker.global.protectedTags).tree
  let after := S04FinalReturnVariantsInput.afterPop #[] result accounted currentTracker borrowFrame argumentCurrent.priorMemory destinationCurrent.id destinationCurrent.entry released
    (currentThread.topUserRelevantFrame.getD 0)
  let done := CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated
  have last : ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent #[] result current) = (done,.ok true) := returned
  have trace := SuccessfulTrace.append prefixTrace (SuccessfulTrace.Trace.next last (.refl _))
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
    ⟨PreparedContracts.actualConfig options () (remaining+1) span,limits,fun _ _ => True⟩
  have entry : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] frame machine) := by
    simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have exited : CallSafety.pastCallBoundary 1 done := by
    change (0 : Nat) < 1
    decide
  exact ⟨done,trace,rfl,rfl,SuccessfulTrace.no_errors safety 1 _ done entry trace exited,
    SuccessfulTrace.no_ub safety 1 _ done entry trace exited⟩

end
end DuplicatePrefix.S03EmptyPositiveReturnWildcard
