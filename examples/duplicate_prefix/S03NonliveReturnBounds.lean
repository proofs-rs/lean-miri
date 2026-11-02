import duplicate_prefix.S03FinalReturnBounds
import duplicate_prefix.S03NonliveEmptyBody
import duplicate_prefix.S03EmptyIntegerTransport

namespace DuplicatePrefix.S03NonliveReturnBounds
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open S03FinalReturnInputBounds S04FinalReturnVariantsInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Actual positive-count nonlive concrete empty body and original Return rule,
from one current post-init state, with a general current return destination.
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
    (returnTag : BorTag) (child selected : UniIndex) (maximum : Option BorTag)
    (returnNode : TreeNode)
    (argument : ArgumentProtection machine.memory borrowFrame destination.id destination.entry returnTag)
    (returnTagged : destination.entry.allocation.extra.indexOfTag returnTag = some child)
    (returnPresent : destination.entry.allocation.extra.nodeAt child = some returnNode)
    (returnSame : returnNode.tag = returnTag) (returnEdge : returnNode.parent = some destination.parent)
    (returnHidden : returnNode.isExposed = false)
    (hiddenFrame : S04ReturnReleaseParent.HiddenFrame destination.entry.allocation.extra borrowFrame)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra tracker.global)
    (positive : DuplicatePrefixBorrowAuthorization.Positive destination.entry.allocation.extra tracker.global.protectedTags
      (some child) (some selected) maximum destination.offset 1)
    (distinct : destination.entry.allocation.extra.roots.toList.Nodup)
    (order : ∀ valid : 0 < destination.entry.allocation.extra.roots.size,
      selected ≠ destination.entry.allocation.extra.roots[0] →
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder destination.entry.allocation.extra)
    (short : destination.entry.allocation.extra.nodes.size < 65536)
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
    (tags : Fin 6 → BorTag) (tagDistinct : Function.Injective tags)
    (argumentId : AllocId) (metadataTag : Option BorTag) (base offset count : UInt64)
    (nonnullAddress : base+offset ≠ 0) (countNonzero : count ≠ 0)
    (nonliveMetadata : DuplicatePrefixEmptyReferenceInput.Metadata machine.memory argumentId metadataTag)
    (absent : machine.memory.live.find? (fun row => row.1 == argumentId) = none)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == argumentId) = some ⟨argumentId,base⟩)
    (nextTag : tracker.global.nextPointerTag = tags 2)
    (lenTag : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag = tags 3)
    (source1 : (frame.locals[1]'(by omega)).value = .live (.immediate
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete argumentId (tags 1)) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm))
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
  obtain ⟨result,current,currentTracker,prefixTrace,fb,fi,ff,fe,frp,frc,fva,fli,fsz,resultLocation,result0,allResult,
      memoryEq,currentTracked,sameMode,sameGlobal,counter,currentGhost,currentShallow,currentRace,currentFixed,currentUnchecked,currentNoGc,
      addressesEq,typesEq,backendEq,extrasEq,currentActive⟩ := S03NonliveEmptyBody.to_return
    options limits remaining span source cmp precise implicitWrites debugOff dynamicFuel fuel dynamicEq validationFuel
    frame machine tags tagDistinct argumentId metadataTag base offset count nonnullAddress countNonzero nonliveMetadata absent cachedAddress frameSize source1 cached1 live2 cached2 dead3 uncached3 dead4 dead5
    uncached4 uncached5 unused sourceBody identity callee location noLocalClocks immediateLocals tracker enabled defaultMode fresh nextTag lenTag runtime.below.protectors
    ghost shallow unchecked noGc fixed metadata notConstructed budget dispatchFuel tagRoomNext race backend thread active
    topZero live0 uncached0 live13 cached13
  let destinationCurrent := S03EmptyIntegerTransport.concrete destination memoryEq addressesEq
  have argumentCurrent : ArgumentProtection current.memory borrowFrame destination.id destination.entry returnTag := by
    rw [memoryEq]
    exact argument
  have protectedEq := congrArg GlobalState.protectedTags sameGlobal
  have currentRuntime := S03EmptyIntegerTransport.runtime destination.entry.allocation.extra tracker.global currentTracker.global
    runtime sameGlobal (by omega)
  have currentPositive : DuplicatePrefixBorrowAuthorization.Positive destination.entry.allocation.extra currentTracker.global.protectedTags
      (some child) (some selected) maximum destination.offset 1 := by
    rw [protectedEq]
    exact positive
  obtain ⟨currentThread,currentThreadActive⟩ := currentActive
  have valid0 : (0 : MIR.LocalId) < result.locals.size := by rw [fsz];decide
  have slot0 : result.locals[0] = ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans result0)
  have currentExtras : current.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) =
      some (destination.id,⟨none,sync⟩) := by
    rw [extrasEq]
    exact extras
  obtain ⟨updated,returned,_,_,_⟩ := S03FinalReturnBounds.step options limits remaining span result current currentTracker borrowFrame
    currentTracked (by rw [fe];exact frameTracked) place destinationCurrent returnTag child selected maximum returnNode argumentCurrent
    returnTagged returnPresent returnSame returnEdge returnHidden hiddenFrame
    currentRuntime currentPositive distinct order short activity currentThread currentThreadActive currentRace
    (backendEq.trans backend) currentGhost currentShallow sync currentExtras outside false fuel debugOff validationFuel
    (fb.trans sourceBody) resultLocation valid0 (by rw [slot0]) (by rw [slot0]) (by rw [fe];exact noLocalClocks)
    (by rw [frp];exact returnPlace) (frc.trans continuation) allResult (fva.trans varargs)
    currentUnchecked currentNoGc currentFixed
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span result current
  let released := (destination.entry.allocation.extra.releaseProtector returnTag currentTracker.global.protectedTags).tree
  let after := S04FinalReturnVariantsInput.afterPop #[] result accounted currentTracker borrowFrame argumentCurrent.priorMemory destination.id destination.entry released
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
end DuplicatePrefix.S03NonliveReturnBounds
