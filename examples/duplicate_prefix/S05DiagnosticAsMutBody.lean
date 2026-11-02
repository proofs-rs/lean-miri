import duplicate_prefix.S05DiagnosticAsMutCall
import duplicate_prefix.AsMutInitializedShape
import duplicate_prefix.AsMutPtrBody
import duplicate_prefix.AsMutPtrReturn
import duplicate_prefix.MemoryCopyBridge
namespace DuplicatePrefix.S05DiagnosticAsMutBody
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess AsMutUncachedCall
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem direct_of_slots (frame : CompilerFrameContext.ActualFrame) (size : frame.locals.size = 5)
    (value0 value1 : Immediate Provenance)
    (zero : frame.locals[0]?.map (·.value) = some (.live (.immediate value0)))
    (one : frame.locals[1]?.map (·.value) = some (.live (.immediate value1)))
    (two : frame.locals[2]?.map (·.value) = some .dead)
    (three : frame.locals[3]?.map (·.value) = some .dead)
    (four : frame.locals[4]?.map (·.value) = some .dead) :
    ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory) := by
  intro slot member memory
  obtain ⟨i,valid,equal⟩ := Array.mem_iff_getElem.mp member
  subst slot
  have upper : i < 5 := by omega
  have known : frame.locals[i]?.map (·.value) = some (frame.locals[i].value) := by simp only [Array.getElem?_eq_getElem valid,Option.map_some]
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- Actual source call step and ten helper MIR statements, with the exact computed
machine retained for subsequent protector release and Return. -/
theorem before_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining budget : Nat)
    (dispatchFuel : limits.callDispatch = budget+1)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (treeEq : entry.allocation.extra = S05DiagnosticAsMutRead.tree)
    (parentEq : parentTag = S05DiagnosticFnEntryRead.tag 12)
    (offsetEq : offset = 0) (lenEq : len = 2)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (nextEq : tracker.global.nextPointerTag = S05DiagnosticFnEntryRead.tag 13)
    (protectedEq : tracker.global.protectedTags = S05DiagnosticSharedRead.protections)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (body : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (located : caller.location = .mir ⟨6,8⟩)
    (source : PreparedContracts.SourceComparator)
    (valid16 : (16 : MIR.LocalId) < caller.locals.size)
    (value16 : caller.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))
      len ActualReferenceMetadata.reference).imm))
    (cached16 : caller.locals[16].layout = some ActualReferenceMetadata.reference)
    (destValid : 15 < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[15].value = .live (.immediate old))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) caller machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) caller machine)).entries.any (·.value.ty == 4) = false)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) (cachedCaller caller destValid) machine)
      (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) (cachedCaller caller destValid) machine)
      (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (machineEq : machine = AsMutPtrReturn.accountedMachine options remaining span beforeMachine)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl beforeMachine.user).gcInterval = 0)
    (fixed : beforeMachine.threads.fixedScheduling = true) :
    let cfg := config options remaining span
    let before := Storage.withCurrent (#[] : Array CompilerFrameContext.ActualFrame) (cachedCaller caller destValid) machine
    let destination := (LocalPlaces.localRuntimePlace (#[] : Array CompilerFrameContext.ActualFrame).size (cachedCaller caller destValid) 15 CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := S05DiagnosticAsMutInstall.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    let frame := AsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag
    ∃ done : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] caller beforeMachine)
        (Storage.withCurrent #[cachedCaller caller destValid] done resultMachine) ∧
      done.body = HelperCompilerFacts.asMutPtrBody.body ∧ done.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity ∧
      done.functionInstance = HelperCompilerFacts.asMutPtrCall.callee ∧ done.locals.size = 5 ∧ done.location = .mir ⟨0,10⟩ ∧
      done.locals[0]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer
        (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      done.locals[1]? = frame.locals[1]? ∧
      done.locals[2]?.map (·.value) = some .dead ∧ done.locals[3]?.map (·.value) = some .dead ∧ done.locals[4]?.map (·.value) = some .dead ∧
      done.extra = frame.extra ∧ done.extra.borrowTracker = some (({} : FrameState).addProtector id tracker.global.nextPointerTag) ∧
      done.extra.dataRace = none ∧ done.returnPlace = destination ∧ done.returnContinuation = .goto (some 7) .Continue ∧ done.vaList = #[] ∧
      (∀ slot ∈ done.locals, ∀ memory, slot.value ≠ .live (.indirect memory)) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let cf := cachedCaller caller destValid
  let before := Storage.withCurrent #[] cf machine
  let destination := (LocalPlaces.localRuntimePlace 0 cf 15 CopyCompilerFacts.destPointerLayout).stackView
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let pointer : Pointer Provenance := Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer len ActualReferenceMetadata.reference).imm
  let post := (AsMutPush.completed options.userRelevantCrates before destination current).machine
  let finalTree := S05DiagnosticAsMutInstall.finalTree entry.allocation.extra tracker parentTag offset len
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine post tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory post.memory id entry finalTree}
  let frame := AsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag
  have call := S05DiagnosticAsMutCall.positive options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len parentTag treeEq parentEq offsetEq lenEq positive nonzero signedFits bounds caller machine tracker enabled nextEq protectedEq fresh
    body identity callee located source valid16 value16 cached16 destValid old destLive uncached callerClocks ghost shallow cachedAddress present race backend
    metadata notConstructed thread index current active top topPresent
  have accounting := SourceControl.before_terminator cfg limits () (Storage.withCurrent #[] caller beforeMachine)
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks cfg limits).beforeTerminator () (Storage.withCurrent #[] caller beforeMachine) =
      (Storage.withCurrent #[] caller machine,.ok ()) := by
    simpa only [machineEq,AsMutPtrReturn.accountedMachine,SourceControl.accounted,Storage.withCurrent,cfg] using accounting
  have entered : ExecutionMachine.step cfg limits () (Storage.withCurrent #[] caller beforeMachine) =
      (Storage.withCurrent #[cf] frame resultMachine,.ok true) := by
    let block := RootBody.reflected.body.body.basicBlocks[6]'(by with_unfolding_all decide +kernel)
    have blockAt : caller.body.basicBlocks[6]? = some block := by rw [body];simp [block]
    have noStatement : block.statements[8]? = none := by with_unfolding_all rfl
    apply GenericCallStages.source_step cfg limits () (Storage.withCurrent #[] caller beforeMachine) (Storage.withCurrent #[] caller machine) _ caller ⟨6,8⟩ block
      HelperCompilerFacts.asMutPtrCall.function #[AsMutEvaluateCall.argument] ⟨15,#[]⟩ (some 7) .Continue AsMutCallTerminator.sourceKind AsMutCallTerminator.fnSpan
      (by simp [Storage.withCurrent,Stack.currentFrame?]) located blockAt noStatement AsMutCallTerminator.source_call accounting' call.2
    simp [Storage.withCurrent]
  have fields : resultMachine.user.payload.ghost = machine.user.payload.ghost ∧
      resultMachine.user.payload.validation = machine.user.payload.validation ∧ resultMachine.user.addresses = machine.user.addresses ∧
      resultMachine.user.payload.payload.user = machine.user.payload.payload.user := by
    dsimp only [resultMachine,TypedBorrowSteps.registeredMachine,ReferenceBorrowDriver.allocatedMachine,post,
      AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact ⟨rfl,rfl,rfl,rfl⟩
  let resultEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra finalTree}
  have resultPresent : resultMachine.memory.live.find? (fun row => row.1 == id) = some (id,resultEntry) :=
    MemoryCopyBridge.live_lookup_replaced post.memory id resultEntry
  have carrier : AsMutPtrCarrier.Valid resultMachine (.inl pointer) len :=
    .positive id tracker.global.nextPointerTag base offset len resultEntry (by rw [fields.2.2.1];exact cachedAddress)
      resultPresent positive nonzero signedFits bounds
  have slots := AsMutInitializedShape.locals options before destination value adjusted id tracker.global.nextPointerTag
  have frameFacts := AsMutInitializedShape.fixed options before destination value adjusted id tracker.global.nextPointerTag
  have size : frame.locals.size = 5 := by rw [show frame.locals = _ from slots];rfl
  have frameRace : frame.extra.dataRace = none := by
    change machine.dataRace.map _ = none
    rw [race];rfl
  obtain ⟨done,trace,bodyDone,identityDone,calleeDone,extra,returnPlace,continuation,varargs,localsId,sourceDone,sizeDone,locationDone,pointerDone,dead2,dead3,dead4⟩ :=
    AsMutPtrBody.actual_ten_statements options limits remaining span debugOff validityFuel validationEq
      #[cf] frame resultMachine pointer len carrier size
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      (by simp only [show frame.locals = _ from slots];rfl)
      frameFacts.1 frameFacts.2.1 frameFacts.2.2.1 frameFacts.2.2.2.1 frameRace
      (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag)
      rfl defaultMode (fields.1.trans ghost) (fields.2.1.trans shallow) dynamicFuel fuelEq cmp
      (by change resultMachine.user.payload.payload.user.types.metadata = _;rw [fields.2.2.2];exact metadata)
      (by change resultMachine.user.payload.payload.user.types.entries.any _ = _;rw [fields.2.2.2];exact notConstructed)
  have direct := direct_of_slots done sizeDone _ adjusted
    (by rw [pointerDone];rfl) (by rw [sourceDone,slots];rfl) dead2 dead3 dead4
  refine ⟨done,.next entered trace,bodyDone.trans frameFacts.1,identityDone.trans frameFacts.2.1,
    calleeDone.trans frameFacts.2.2.1,sizeDone,locationDone,pointerDone,sourceDone,dead2,dead3,dead4,extra,?_,?_,?_,?_,?_,direct⟩
  · rw [extra];exact frameFacts.2.2.2.2.2.2.2
  · rw [extra];exact frameRace
  · exact returnPlace.trans frameFacts.2.2.2.2.1
  · exact continuation.trans frameFacts.2.2.2.2.2.1
  · exact varargs.trans frameFacts.2.2.2.2.2.2.1

#print axioms before_return
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DiagnosticAsMutBody." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved diagnostic as_mut body dependency {dependency}"
end
end DuplicatePrefix.S05DiagnosticAsMutBody
