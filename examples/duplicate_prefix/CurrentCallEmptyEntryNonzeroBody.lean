import duplicate_prefix.CurrentCallEmptyEntryFrame
import duplicate_prefix.S03EmptyPositiveBodyExact
import duplicate_prefix.S03EmptyIntegerBody
import duplicate_prefix.DuplicatePrefixTypeCacheOrigins
namespace DuplicatePrefix.CurrentCallEmptyEntryNonzeroBody
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
open CurrentCallEmptyTypedEntry CurrentCallEmptyEntryFrame
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Actual installed empty-entry frame through Shared and len to Return false.
Current constructor metadata is internal physical data; no legacy ownership
packet or operation-success premise is used. -/
theorem live_from_installed {options before initialTracker argument}
    (effect : Effect options before initialTracker argument)
    (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (root firstDone : RootFrame)
    (raw : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (copied : firstDone.frame = resultFrame effect remaining span (firstLive root).frame {} 1 ((firstLive root).valid i1))
    (borrow : FrameState) (boolId : AllocId) (boolTag : BorTag)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker)
    (parentTag newTag : BorTag) (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset count : UInt64) (nonzero : base+offset≠0) (countNonzero : count≠0)
    (representation : adjusted effect remaining span = (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm)
    (input : EmptyForestSharedPool.Input entry.allocation.extra parentTag newTag)
    (nextTag : tracker.global.nextPointerTag=newTag)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id)=some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1==id)=some (id,entry))
    (borrowRuntime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (dynamicFuel validityFuel budget : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1) (validityEq : options.limits.validation=validityFuel+1)
    (dispatchFuel : limits.callDispatch=budget+1)
    (tagRoomNext : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (nodeRoomTwo : entry.allocation.extra.nodes.size+2≤4294967295)
    (thread : Miri.Concurrency.ThreadRecord) (activeThread : machine.threads.activeThread?=some thread)
    (topZero : thread.topUserRelevantFrame=some 0) :
    let frame := installed firstDone count borrow boolId boolTag
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
      (∃ finalThread, finalMachine.threads.activeThread? = some finalThread) := by
  dsimp only
  let frame := installed firstDone count borrow boolId boolTag
  obtain ⟨body,identity,callee,location,size,clocks⟩ := installed_control firstDone count borrow boolId boolTag
  have cells (i : Fin 25) := installed_slot effect remaining span root firstDone raw copied count borrow boolId boolTag i
  have slots (i : Fin 25) := Option.some.inj ((Array.getElem?_eq_getElem (by rw [size];exact i.isLt)).symm.trans (cells i))
  have immediate := installed_immediate effect remaining span root firstDone raw copied count borrow boolId boolTag
  obtain ⟨current,enabled,mode⟩ := model.defaultTracker
  have equal : current=tracker := Option.some.inj (enabled.symm.trans tracked)
  subst current
  have source1 : (frame.locals[1]'(by rw [size];decide)).value=.live (.immediate (adjusted effect remaining span)) := by
    simpa [frame] using congrArg LocalState.value (slots ⟨1,by decide⟩)
  rw [representation] at source1
  have unused : ∀ i (valid:i<frame.locals.size),7≤i→i≤12→frame.locals[i]'valid=⟨.dead,none⟩ := by
    intro i valid low high
    have bound : i<25 := by rw [size] at valid;exact valid
    have cell := slots ⟨i,bound⟩
    simpa [show (14:Nat)≠i by omega,show (13:Nat)≠i by omega,show (6:Nat)≠i by omega,
      show (0:Nat)≠i by omega,show (2:Nat)≠i by omega,show (1:Nat)≠i by omega] using cell
  exact S03EmptyPositiveBodyExact.to_return options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span machine model) model.nullComparator
    model.preciseOff model.implicitOff model.debugOff dynamicFuel validityFuel dynamicEq validityEq frame machine
    parentTag newTag id entry base offset count nonzero countNonzero input size source1
    (by simpa using congrArg LocalState.layout (slots ⟨1,by decide⟩))
    (by simpa using congrArg LocalState.value (slots ⟨2,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨2,by decide⟩))
    (by simpa using congrArg LocalState.value (slots ⟨3,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨3,by decide⟩))
    (by simpa using congrArg LocalState.value (slots ⟨4,by decide⟩))
    (by simpa using congrArg LocalState.value (slots ⟨5,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨4,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨5,by decide⟩)) unused body identity callee location clocks immediate
    tracker tracked mode nextTag fresh cachedAddress present model.ghostOff model.shallow model.unchecked model.noGc
    model.fixedScheduler model.metadata (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ model.metadata origins)
    borrowRuntime budget dispatchFuel tagRoomNext nodeRoomTwo model.noDataRace model.noBackend thread activeThread topZero
    (by simpa using congrArg LocalState.value (slots ⟨0,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨0,by decide⟩))
    (by simpa using congrArg LocalState.value (slots ⟨13,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨13,by decide⟩))

theorem integer_from_installed {options before initialTracker argument}
    (effect : Effect options before initialTracker argument)
    (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (root firstDone : RootFrame)
    (raw : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (copied : firstDone.frame = resultFrame effect remaining span (firstLive root).frame {} 1 ((firstLive root).valid i1))
    (borrow : FrameState) (boolId : AllocId) (boolTag : BorTag)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker)
    (address count : UInt64) (nonzero : address≠0) (countNonzero : count≠0)
    (representation : adjusted effect remaining span =
      (RetagReferencePlace.integerSliceValue address 0 ActualReferenceMetadata.reference).imm)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (dynamicFuel validityFuel budget : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1) (validityEq : options.limits.validation=validityFuel+1)
    (dispatchFuel : limits.callDispatch=budget+1)
    (tagRoomNext : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (thread : Miri.Concurrency.ThreadRecord) (activeThread : machine.threads.activeThread?=some thread)
    (topZero : thread.topUserRelevantFrame=some 0) :
    let frame := installed firstDone count borrow boolId boolTag
    ∃ result : CompilerFrameContext.ActualFrame,
      ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      ∃ finalTracker : MachineHooks.BorrowState,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result finalMachine) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧ result.locals.size = 25 ∧
      result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧
      finalMachine.memory = machine.memory ∧
      finalMachine.borrowTracker = some finalTracker ∧ finalTracker.retagMode = tracker.retagMode ∧
      finalTracker.global = {tracker.global with nextPointerTag := finalTracker.global.nextPointerTag} ∧
      finalTracker.global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+2 ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      (∃ finalThread, finalMachine.threads.activeThread? = some finalThread) := by
  dsimp only
  let frame := installed firstDone count borrow boolId boolTag
  obtain ⟨body,identity,callee,location,size,clocks⟩ := installed_control firstDone count borrow boolId boolTag
  have cells (i : Fin 25) := installed_slot effect remaining span root firstDone raw copied count borrow boolId boolTag i
  have slots (i : Fin 25) := Option.some.inj ((Array.getElem?_eq_getElem (by rw [size];exact i.isLt)).symm.trans (cells i))
  have immediate := installed_immediate effect remaining span root firstDone raw copied count borrow boolId boolTag
  obtain ⟨current,enabled,mode⟩ := model.defaultTracker
  have equal : current=tracker := Option.some.inj (enabled.symm.trans tracked)
  subst current
  have source1 : (frame.locals[1]'(by rw [size];decide)).value=.live (.immediate (adjusted effect remaining span)) := by
    simpa [frame] using congrArg LocalState.value (slots ⟨1,by decide⟩)
  rw [representation] at source1
  have unused : ∀ i (valid:i<frame.locals.size),7≤i→i≤12→frame.locals[i]'valid=⟨.dead,none⟩ := by
    intro i valid low high
    have bound : i<25 := by rw [size] at valid;exact valid
    have cell := slots ⟨i,bound⟩
    simpa [show (14:Nat)≠i by omega,show (13:Nat)≠i by omega,show (6:Nat)≠i by omega,
      show (0:Nat)≠i by omega,show (2:Nat)≠i by omega,show (1:Nat)≠i by omega] using cell
  exact S03EmptyIntegerBody.to_return options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span machine model) model.nullComparator
    model.preciseOff model.implicitOff model.debugOff dynamicFuel validityFuel dynamicEq validityEq frame machine
    address count nonzero countNonzero size source1
    (by simpa using congrArg LocalState.layout (slots ⟨1,by decide⟩))
    (by simpa using congrArg LocalState.value (slots ⟨2,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨2,by decide⟩))
    (by simpa using congrArg LocalState.value (slots ⟨3,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨3,by decide⟩))
    (by simpa using congrArg LocalState.value (slots ⟨4,by decide⟩))
    (by simpa using congrArg LocalState.value (slots ⟨5,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨4,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨5,by decide⟩)) unused body identity callee location clocks immediate
    tracker tracked mode fresh model.ghostOff model.shallow model.unchecked model.noGc
    model.fixedScheduler model.metadata (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ model.metadata origins)
    budget dispatchFuel tagRoomNext model.noDataRace model.noBackend thread activeThread topZero
    (by simpa using congrArg LocalState.value (slots ⟨0,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨0,by decide⟩))
    (by simpa using congrArg LocalState.value (slots ⟨13,by decide⟩))
    (by simpa using congrArg LocalState.layout (slots ⟨13,by decide⟩))

end
end DuplicatePrefix.CurrentCallEmptyEntryNonzeroBody
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryNonzeroBody" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty nonzero body dependency {dependency}"
