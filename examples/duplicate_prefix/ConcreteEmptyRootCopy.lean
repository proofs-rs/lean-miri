import duplicate_prefix.ConcreteEmptyReferenceArgumentCopy
namespace DuplicatePrefix.ConcreteEmptyRootCopy
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def changedFrame (frame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId)
    (value : Immediate Provenance) (valid : localId < frame.locals.size) (borrowFrame : FrameState) (id : AllocId) (tag : BorTag) :=
  TypedBorrowSteps.registeredFrame (ConcreteEmptyReferenceArgumentCopy.copiedFrame frame localId value valid) borrowFrame id tag

def changedMachine (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parent : BorTag) (capacity : UInt64) :=
  {machine with
    borrowTracker := some ⟨TypedRetagGeneric.protectedGlobal global fresh,.FnEntry⟩
    memory := RetagEntry.updatedMemory machine.memory id entry (TypedRetagConcreteEmpty.lazyTree parent global.nextPointerTag capacity)}

def nonliveMachine (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615) :=
  {machine with borrowTracker := some ⟨TypedRetagGeneric.protectedGlobal global fresh,.FnEntry⟩}

theorem copy
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (global : GlobalState)
    (base offset capacity : UInt64) (nonzero : base+offset ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference) (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global,.FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (distinct : parentTag ≠ global.nextPointerTag)
    (root : entry.allocation.extra = BorrowTree.new parentTag (Size.ofBytes capacity))
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance) (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference).imm
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,reference⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (changedFrame frame localId adjusted valid borrowFrame id global.nextPointerTag)
        (changedMachine machine global fresh id entry parentTag capacity)) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference).imm
  let copied := ConcreteEmptyReferenceArgumentCopy.copiedFrame frame localId value valid
  let afterFrame := TypedBorrowSteps.registeredFrame copied borrowFrame id global.nextPointerTag
  let afterMachine := changedMachine {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
    global fresh id entry parentTag capacity
  have result := ConcreteEmptyReferenceArgumentCopy.copy_live_argument options limits remaining span ctx debugOff cmp dynamicFuel validityFuel
    fuelEq validationEq id parentTag global base offset capacity nonzero entry frames frame machine localId valid old
    live cached noClocks ghost shallow cachedAddress present borrowFrame frameBorrow enabled fresh distinct root
    metadata notConstructed afterFrame afterMachine rfl rfl rfl rfl view destination
  have restored : {machine.user with payload := {machine.user.payload with ghost := false}} = machine.user := by
    rw [← ghost]
  have afterValid : localId < afterFrame.locals.size := by
    simpa [afterFrame,copied,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,ConcreteEmptyReferenceArgumentCopy.copiedFrame] using valid
  have frameEq : {afterFrame with locals := (afterFrame.locals.set localId
      {value := .live (.immediate adjusted),layout := afterFrame.locals[localId].layout} afterValid)} =
      changedFrame frame localId adjusted valid borrowFrame id global.nextPointerTag := by
    simp [changedFrame,afterFrame,copied,ConcreteEmptyReferenceArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,
      TypedRetagEntry.frameWithBorrow,Array.set_set]
  have machineEq : {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}} =
      changedMachine machine global fresh id entry parentTag capacity := by
    dsimp only [afterMachine,changedMachine]
    rw [restored]
  dsimp only
  simpa only [value,adjusted,frameEq,machineEq] using result
theorem copy_nonlive
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (global : GlobalState)
    (base offset : UInt64) (nonzero : base+offset ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference) (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global,.FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (info : AllocationInfo) (allocationInfo : machine.memory.getAllocInfo id = .ok info)
    (nonlive : info.kind ≠ .liveData)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance) (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference).imm
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,reference⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (changedFrame frame localId adjusted valid borrowFrame id global.nextPointerTag)
        (nonliveMachine machine global fresh)) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) 0 reference).imm
  let copied := ConcreteEmptyReferenceArgumentCopy.copiedFrame frame localId value valid
  let afterFrame := TypedBorrowSteps.registeredFrame copied borrowFrame id global.nextPointerTag
  let afterMachine := nonliveMachine {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
    global fresh
  have result := ConcreteEmptyReferenceArgumentCopy.copy_nonlive_argument options limits remaining span ctx debugOff cmp dynamicFuel validityFuel
    fuelEq validationEq id parentTag global base offset nonzero frames frame machine localId valid old
    live cached noClocks ghost shallow cachedAddress borrowFrame frameBorrow enabled fresh info allocationInfo nonlive
    metadata notConstructed afterFrame afterMachine rfl rfl rfl rfl view destination
  have restored : {machine.user with payload := {machine.user.payload with ghost := false}} = machine.user := by
    rw [← ghost]
  have afterValid : localId < afterFrame.locals.size := by
    simpa [afterFrame,copied,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,ConcreteEmptyReferenceArgumentCopy.copiedFrame] using valid
  have frameEq : {afterFrame with locals := (afterFrame.locals.set localId
      {value := .live (.immediate adjusted),layout := afterFrame.locals[localId].layout} afterValid)} =
      changedFrame frame localId adjusted valid borrowFrame id global.nextPointerTag := by
    simp [changedFrame,afterFrame,copied,ConcreteEmptyReferenceArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,
      TypedRetagEntry.frameWithBorrow,Array.set_set]
  have machineEq : {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}} =
      nonliveMachine machine global fresh := by
    dsimp only [afterMachine,nonliveMachine]
    rw [restored]
  dsimp only
  simpa only [value,adjusted,frameEq,machineEq] using result
end
end DuplicatePrefix.ConcreteEmptyRootCopy

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ConcreteEmptyRootCopy.copy, ``DuplicatePrefix.ConcreteEmptyRootCopy.copy_nonlive] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved concrete empty root argument dependency {dependency}"
