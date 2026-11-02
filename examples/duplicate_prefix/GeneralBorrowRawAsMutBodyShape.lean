import duplicate_prefix.GeneralBorrowRawAsMutShape
import duplicate_prefix.GeneralBorrowRawFnEntryResources
import duplicate_prefix.AsMutPtrBody
import duplicate_prefix.MemoryCopyBridge
namespace DuplicatePrefix.GeneralBorrowRawAsMutBodyShape
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
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

/-- Actual protected helper initialization followed by all ten pure MIR statements.
The body leaves memory/tracker unchanged and returns the actual fresh-child pointer;
protector release and return are intentionally subsequent operations. -/
theorem before_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (raw : GeneralBorrowRawFnEntry.Input entry.allocation.extra tracker.global)
    (rawTag : raw.parentTag = parentTag) (rawOffset : raw.offset = offset) (rawLen : raw.len = len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (destId : MIR.LocalId) (destValid : destId < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[destId].value = .live (.immediate old))
    (destCached : caller.locals[destId].layout = some CopyCompilerFacts.destPointerLayout)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).entries.any (·.value.ty == 4) = false)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current) :
    let cfg := config options remaining span
    let before := Storage.withCurrent frames caller machine
    let destination := (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := GeneralBorrowRawFnEntryArgument.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    let frame := GeneralBorrowRawAsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag
    ∃ done : CompilerFrameContext.ActualFrame,
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
      #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩] false destination (.goto (some 7) .Continue) before =
      .ok () (Storage.withCurrent (frames.push caller)
        (GeneralBorrowRawAsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine) ∧
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent (frames.push caller) frame resultMachine)
        (Storage.withCurrent (frames.push caller) done resultMachine) ∧
      done.location = .mir ⟨0,10⟩ ∧
      done.locals[0]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer
        (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset)))))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      done.body = HelperCompilerFacts.asMutPtrBody.body ∧ done.locals.size = 5 ∧
      done.locals[1]? = frame.locals[1]? ∧
      (done.locals[2]?.map (·.value)) = some .dead ∧
      (done.locals[3]?.map (·.value)) = some .dead ∧
      (done.locals[4]?.map (·.value)) = some .dead ∧
      done.vaList = #[] ∧
      (∀ slot ∈ done.locals, ∀ memory, slot.value ≠ .live (.indirect memory)) ∧
      done.extra = frame.extra ∧ done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree
        (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      ∃ child, finalTree.indexOfTag tracker.global.nextPointerTag = some child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree
          (TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags
          (some child) (some raw.selected) raw.maximum offset len) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin finalTree child .Write offset (offset+len) := by
  let before := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let pointer : Pointer Provenance := Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base pointer len ActualReferenceMetadata.reference).imm
  let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
  let finalTree := GeneralBorrowRawFnEntryArgument.finalTree entry.allocation.extra tracker parentTag offset len
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
    (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
    memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
  let frame := GeneralBorrowRawAsMutEntry.initialized options before destination value adjusted id tracker.global.nextPointerTag
  have entered := GeneralBorrowRawAsMutEntry.actual_entry options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len parentTag positive nonzero signedFits bounds frames caller machine tracker enabled defaultMode fresh
    runtime raw rawTag rawOffset rawLen capacity destId destValid old destLive destCached callerClocks ghost shallow cachedAddress present race
    metadata notConstructed thread index current active top topPresent
  have fields : resultMachine.user.payload.ghost = machine.user.payload.ghost ∧
      resultMachine.user.payload.validation = machine.user.payload.validation ∧
      resultMachine.user.addresses = machine.user.addresses ∧
      resultMachine.user.payload.payload.user = machine.user.payload.payload.user := by
    dsimp only [resultMachine,TypedBorrowSteps.registeredMachine,ReferenceBorrowDriver.allocatedMachine,postMachine,
      AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact ⟨rfl,rfl,rfl,rfl⟩
  let resultEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra finalTree}
  have resultPresent : resultMachine.memory.live.find? (fun row => row.1 == id) = some (id,resultEntry) :=
    MemoryCopyBridge.live_lookup_replaced postMachine.memory id resultEntry
  have carrier : AsMutPtrCarrier.Valid resultMachine (.inl pointer) len :=
    .positive id tracker.global.nextPointerTag base offset len resultEntry (by rw [fields.2.2.1];exact cachedAddress)
      resultPresent positive nonzero signedFits bounds
  have slots := GeneralBorrowRawAsMutShape.locals options before destination value adjusted id tracker.global.nextPointerTag
  have frameFacts := GeneralBorrowRawAsMutShape.fixed options before destination value adjusted id tracker.global.nextPointerTag
  have size : frame.locals.size = 5 := by rw [show frame.locals = _ from slots];rfl
  have frameRace : frame.extra.dataRace = none := by
    change ((AsMutPush.fresh before.machine).1.dataRace.map _) = none
    change machine.dataRace.map _ = none
    rw [race];rfl
  obtain ⟨done,trace,body,identity,callee,extra,returnPlace,continuation,varargs,localsId,source,sizeDone,location,pointerDone,dead2,dead3,dead4⟩ :=
    AsMutPtrBody.actual_ten_statements options limits remaining span debugOff validityFuel validationEq
      (frames.push caller) frame resultMachine pointer len carrier size
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
  have resources := GeneralBorrowRawFnEntryResources.resources entry.allocation.extra tracker {} id runtime raw
  simp only [rawTag,rawOffset,rawLen] at resources
  obtain ⟨borrowRuntime,_,_,_,held,_,_,child,lookup,childPositive,activity⟩ := resources
  have direct := direct_of_slots done sizeDone _ adjusted
    (by rw [pointerDone];rfl) (by rw [source,slots];rfl) dead2 dead3 dead4
  exact ⟨done,entered,trace,location,pointerDone,body.trans frameFacts.1,sizeDone,source,dead2,dead3,dead4,
    varargs.trans frameFacts.2.2.2.2.2.2.1,direct,extra,returnPlace,continuation,borrowRuntime,child,lookup,childPositive,activity⟩
end
end DuplicatePrefix.GeneralBorrowRawAsMutBodyShape
