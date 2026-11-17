import duplicate_prefix.LenEntry
import duplicate_prefix.LenZeroInstall
namespace DuplicatePrefix.LenZeroEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem live_zero
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capacity base offset : UInt64)
    (tree : entry.allocation.extra = tree3 tags
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes capacity) rootLocation))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (nonzero : base+offset ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (nextTag : tracker.global.nextPointerTag = tags 3)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (valid : localId < caller.locals.size) (old : Immediate Provenance)
    (live : caller.locals[localId].value = .live (.immediate old))
    (cached : caller.locals[localId].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (presentFrame : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current)
    (metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView current)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView current)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let state := Storage.withCurrent frames caller machine
    let destination := (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView
    let frame := LenEntry.rawFrame options state destination
    let postMachine := (LenPush.completed options.userRelevantCrates state destination current).machine
    let frameValid : 1 < frame.locals.size := by rw [LenEntry.raw_size]; decide
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm
    let finalTree := tree4 tags (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
    let afterFrame := TypedBorrowSteps.registeredFrame (LenInstall.resultFrame frame frameValid output) {} id tracker.global.nextPointerTag
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      LenHelper.resolved.callee LenHelper.body LenHelper.abi #[.Copy ⟨.immediate value,LenHelper.rawLayout⟩]
      false destination (.goto (some 3) .Continue) state =
      .ok () (Storage.withCurrent (frames.push caller)
        (LenDone.doneFrame {afterFrame with location := .unwinding LenEntryFacts.lenPreamble}) resultMachine) := by
  let cfg := config options remaining span
  let state := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView
  let frame := LenEntry.rawFrame options state destination
  let postMachine := (LenPush.completed options.userRelevantCrates state destination current).machine
  have size : frame.locals.size = 3 := LenEntry.raw_size options state destination
  have valid1 : 1 < frame.locals.size := by rw [size];decide
  have postTracked : postMachine.borrowTracker = some tracker := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact enabled
  have postGhost : postMachine.user.payload.ghost = false := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact ghost
  have postShallow : postMachine.user.payload.validation = .Shallow := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact shallow
  have postAddress : postMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact cachedAddress
  have postPresent : postMachine.memory.live.find? (fun row => row.1 == id) = some (id,entry) := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact present
  have postRace : postMachine.dataRace = none := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact race
  have frameBorrow : frame.extra.borrowTracker = some {} := by
    simp [frame,LenEntry.rawFrame,LenFrame.rawFrame,LenPush.fresh,CallEntryFacts.freshRoot,state,Storage.withCurrent,enabled]
  have frameRace : frame.extra.dataRace = none := by
    simp [frame,LenEntry.rawFrame,LenFrame.rawFrame,LenPush.fresh,CallEntryFacts.freshRoot,state,Storage.withCurrent,race]
  have made := LenZeroInstall.live_zero_scoped options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    tags distinct id entry capacity base offset tree allocationSize nonzero (frames.push caller) frame postMachine
    tracker postTracked {} frameBorrow nextTag fresh valid1 rfl rfl rfl rfl rfl frameRace postGhost postShallow
    postAddress postPresent metadata notConstructed
  let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
    (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm
  let af := TypedBorrowSteps.registeredFrame (LenInstall.resultFrame frame valid1 output) {} id tracker.global.nextPointerTag
  have afSize : af.locals.size = 3 := by
    simpa only [af,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,LenInstall.resultFrame,
      LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,Array.size_set] using size
  have afValid : 0 < af.locals.size := by rw [afSize];decide
  have afDead : af.locals[0].value = .dead := by
    simp [af,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,LenInstall.resultFrame,
      LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,
      Array.getElem_set,frame,LenEntry.rawFrame,LenFrame.rawFrame,Frame.create]
  have afRace : af.extra.dataRace = none := by
    simpa only [af,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,LenInstall.resultFrame,LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame] using frameRace
  exact LenEntry.actual_entry_of_install options limits remaining span debugOff frames caller machine tracker enabled _
    localId valid old live cached noClocks race ghost shallow thread index current active top presentFrame _ _ made
    rfl rfl rfl afValid afDead afRace

theorem nonlive_zero
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (allocation : AllocationInfo)
    (capacity base offset : UInt64)
    (nonzero : base+offset ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (allocationInfo : machine.memory.getAllocInfo id = .ok allocation)
    (nonlive : allocation.kind ≠ .liveData)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (nextTag : tracker.global.nextPointerTag = tags 3)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (valid : localId < caller.locals.size) (old : Immediate Provenance)
    (live : caller.locals[localId].value = .live (.immediate old))
    (cached : caller.locals[localId].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (race : machine.dataRace = none)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (presentFrame : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current)
    (metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView current)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView current)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let state := Storage.withCurrent frames caller machine
    let destination := (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView
    let frame := LenEntry.rawFrame options state destination
    let postMachine := (LenPush.completed options.userRelevantCrates state destination current).machine
    let frameValid : 1 < frame.locals.size := by rw [LenEntry.raw_size]; decide
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm
    let afterFrame := TypedBorrowSteps.registeredFrame (LenInstall.resultFrame frame frameValid output) {} id tracker.global.nextPointerTag
    let resultMachine := TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      LenHelper.resolved.callee LenHelper.body LenHelper.abi #[.Copy ⟨.immediate value,LenHelper.rawLayout⟩]
      false destination (.goto (some 3) .Continue) state =
      .ok () (Storage.withCurrent (frames.push caller)
        (LenDone.doneFrame {afterFrame with location := .unwinding LenEntryFacts.lenPreamble}) resultMachine) := by
  let cfg := config options remaining span
  let state := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView
  let frame := LenEntry.rawFrame options state destination
  let postMachine := (LenPush.completed options.userRelevantCrates state destination current).machine
  have size : frame.locals.size = 3 := LenEntry.raw_size options state destination
  have valid1 : 1 < frame.locals.size := by rw [size];decide
  have postTracked : postMachine.borrowTracker = some tracker := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact enabled
  have postGhost : postMachine.user.payload.ghost = false := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact ghost
  have postShallow : postMachine.user.payload.validation = .Shallow := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact shallow
  have postAddress : postMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact cachedAddress
  have postInfo : postMachine.memory.getAllocInfo id = .ok allocation := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact allocationInfo
  have postRace : postMachine.dataRace = none := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact race
  have frameBorrow : frame.extra.borrowTracker = some {} := by
    simp [frame,LenEntry.rawFrame,LenFrame.rawFrame,LenPush.fresh,CallEntryFacts.freshRoot,state,Storage.withCurrent,enabled]
  have frameRace : frame.extra.dataRace = none := by
    simp [frame,LenEntry.rawFrame,LenFrame.rawFrame,LenPush.fresh,CallEntryFacts.freshRoot,state,Storage.withCurrent,race]
  have made := LenZeroInstall.nonlive_zero_scoped options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    tags distinct id allocation capacity base offset nonzero (frames.push caller) frame postMachine postInfo nonlive
    tracker postTracked {} frameBorrow nextTag fresh valid1 rfl rfl rfl rfl rfl frameRace postGhost postShallow
    postAddress metadata notConstructed
  let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
    (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm
  let af := TypedBorrowSteps.registeredFrame (LenInstall.resultFrame frame valid1 output) {} id tracker.global.nextPointerTag
  have afSize : af.locals.size = 3 := by
    simpa only [af,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,LenInstall.resultFrame,
      LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,Array.size_set] using size
  have afValid : 0 < af.locals.size := by rw [afSize];decide
  have afDead : af.locals[0].value = .dead := by
    simp [af,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,LenInstall.resultFrame,
      LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,
      Array.getElem_set,frame,LenEntry.rawFrame,LenFrame.rawFrame,Frame.create]
  have afRace : af.extra.dataRace = none := by
    simpa only [af,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,LenInstall.resultFrame,LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame] using frameRace
  exact LenEntry.actual_entry_of_install options limits remaining span debugOff frames caller machine tracker enabled _
    localId valid old live cached noClocks race ghost shallow thread index current active top presentFrame _ _ made
    rfl rfl rfl afValid afDead afRace

theorem integer_zero
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (address : UInt64) (nonzero : address ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (valid : localId < caller.locals.size) (old : Immediate Provenance)
    (live : caller.locals[localId].value = .live (.immediate old))
    (cached : caller.locals[localId].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (race : machine.dataRace = none)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (presentFrame : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current)
    (metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView current)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView current)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let state := Storage.withCurrent frames caller machine
    let destination := (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView
    let frame := LenEntry.rawFrame options state destination
    let postMachine := (LenPush.completed options.userRelevantCrates state destination current).machine
    let frameValid : 1 < frame.locals.size := by rw [LenEntry.raw_size]; decide
    let value := (RetagReferencePlace.integerSliceValue address 0 SharedReferenceMetadata.sharedLayout).imm
    let output := (RetagReferencePlace.integerSliceValue address 0 SharedReferenceMetadata.sharedLayout).imm
    let afterFrame := LenInstall.resultFrame frame frameValid output
    let resultMachine := ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      LenHelper.resolved.callee LenHelper.body LenHelper.abi #[.Copy ⟨.immediate value,LenHelper.rawLayout⟩]
      false destination (.goto (some 3) .Continue) state =
      .ok () (Storage.withCurrent (frames.push caller)
        (LenDone.doneFrame {afterFrame with location := .unwinding LenEntryFacts.lenPreamble}) resultMachine) := by
  let cfg := config options remaining span
  let state := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView
  let frame := LenEntry.rawFrame options state destination
  let postMachine := (LenPush.completed options.userRelevantCrates state destination current).machine
  have size : frame.locals.size = 3 := LenEntry.raw_size options state destination
  have valid1 : 1 < frame.locals.size := by rw [size];decide
  have postTracked : postMachine.borrowTracker = some tracker := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact enabled
  have postGhost : postMachine.user.payload.ghost = false := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact ghost
  have postShallow : postMachine.user.payload.validation = .Shallow := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact shallow
  have postRace : postMachine.dataRace = none := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact race
  have frameBorrow : frame.extra.borrowTracker = some {} := by
    simp [frame,LenEntry.rawFrame,LenFrame.rawFrame,LenPush.fresh,CallEntryFacts.freshRoot,state,Storage.withCurrent,enabled]
  have frameRace : frame.extra.dataRace = none := by
    simp [frame,LenEntry.rawFrame,LenFrame.rawFrame,LenPush.fresh,CallEntryFacts.freshRoot,state,Storage.withCurrent,race]
  have made := LenZeroInstall.integer_zero_scoped options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    address nonzero (frames.push caller) frame postMachine
    tracker postTracked fresh valid1 rfl rfl rfl rfl rfl frameRace postGhost postShallow
    metadata notConstructed
  let output := (RetagReferencePlace.integerSliceValue address 0 SharedReferenceMetadata.sharedLayout).imm
  let af := LenInstall.resultFrame frame valid1 output
  have afSize : af.locals.size = 3 := by
    simpa only [af,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,LenInstall.resultFrame,
      LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,Array.size_set] using size
  have afValid : 0 < af.locals.size := by rw [afSize];decide
  have afDead : af.locals[0].value = .dead := by
    simp [af,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,LenInstall.resultFrame,
      LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,
      Array.getElem_set,frame,LenEntry.rawFrame,LenFrame.rawFrame,Frame.create]
  have afRace : af.extra.dataRace = none := by
    simpa only [af,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,LenInstall.resultFrame,LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame] using frameRace
  exact LenEntry.actual_entry_of_install options limits remaining span debugOff frames caller machine tracker enabled _
    localId valid old live cached noClocks race ghost shallow thread index current active top presentFrame _ _ made
    rfl rfl rfl afValid afDead afRace

open Lean Elab Command in
run_cmd do
  for declaration in [``live_zero, ``nonlive_zero, ``integer_zero] do
   for dependency in (← collectAxioms declaration) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved 0 positive entry {dependency}"
end
end DuplicatePrefix.LenZeroEntry
