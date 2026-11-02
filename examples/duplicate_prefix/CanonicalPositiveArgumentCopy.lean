import duplicate_prefix.PositiveReferenceArgumentCopy
namespace DuplicatePrefix.CanonicalPositiveArgumentCopy
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def changedFrame (frame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId)
    (value : Immediate Provenance) (valid : localId < frame.locals.size) (borrowFrame : FrameState) (id : AllocId) (tag : BorTag) :=
  TypedBorrowSteps.registeredFrame (PositiveReferenceArgumentCopy.copiedFrame frame localId value valid) borrowFrame id tag

def changedMachine (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (parent : BorTag) (capacity offset len : UInt64) :=
  {machine with
    borrowTracker := some ⟨TypedRetagGeneric.protectedGlobal global fresh,.FnEntry⟩
    memory := RetagEntry.updatedMemory machine.memory id entry (TypedRetagGeneric.childTree parent global.nextPointerTag capacity offset len)}

theorem copy
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (global : GlobalState)
    (base offset len capacity : UInt64) (nonzero : base+offset ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounded : len ≤ 9223372036854775807)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
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
    (distinct : parentTag ≠ global.nextPointerTag) (rootUnprotected : global.protectedTags.contains parentTag = false)
    (root : entry.allocation.extra = BorrowTree.new parentTag (Size.ofBytes capacity))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity) (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance) (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) len reference).imm
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,reference⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (changedFrame frame localId adjusted valid borrowFrame id global.nextPointerTag)
        (changedMachine machine global fresh id entry parentTag capacity offset len)) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base+offset))) len reference).imm
  let copied := PositiveReferenceArgumentCopy.copiedFrame frame localId value valid
  let afterFrame := TypedBorrowSteps.registeredFrame copied borrowFrame id global.nextPointerTag
  let afterMachine := changedMachine {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
    global fresh id entry parentTag capacity offset len
  have result := PositiveReferenceArgumentCopy.copy_positive_argument options limits remaining span ctx debugOff cmp dynamicFuel validityFuel
    fuelEq validationEq id parentTag global base offset len capacity nonzero entry positive signedFits bounded bounds frames frame machine localId valid old
    live cached noClocks ghost shallow cachedAddress present borrowFrame frameBorrow enabled fresh distinct rootUnprotected root allocationSize race
    metadata notConstructed afterFrame afterMachine rfl rfl rfl rfl view destination
  have restored : {machine.user with payload := {machine.user.payload with ghost := false}} = machine.user := by
    rw [← ghost]
  have afterValid : localId < afterFrame.locals.size := by
    simpa [afterFrame,copied,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,PositiveReferenceArgumentCopy.copiedFrame] using valid
  have frameEq : {afterFrame with locals := (afterFrame.locals.set localId
      {value := .live (.immediate adjusted),layout := afterFrame.locals[localId].layout} afterValid)} =
      changedFrame frame localId adjusted valid borrowFrame id global.nextPointerTag := by
    simp [changedFrame,afterFrame,copied,PositiveReferenceArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,
      TypedRetagEntry.frameWithBorrow,Array.set_set]
  have machineEq : {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}} =
      changedMachine machine global fresh id entry parentTag capacity offset len := by
    dsimp only [afterMachine,changedMachine]
    rw [restored]
  dsimp only
  simpa only [value,adjusted,frameEq,machineEq] using result
end
end DuplicatePrefix.CanonicalPositiveArgumentCopy
