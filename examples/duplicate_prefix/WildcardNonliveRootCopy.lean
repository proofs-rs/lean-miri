import duplicate_prefix.WildcardNonliveReferenceArgumentCopy
import duplicate_prefix.ConcreteEmptyRootCopy
namespace DuplicatePrefix.WildcardNonliveRootCopy
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
open ConcreteEmptyRootCopy
theorem copy_nonlive
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (global : GlobalState)
    (base : UInt64) (nonzero : base ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference) (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (position : Nat) (positionValid : position < machine.user.addresses.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered machine.user.addresses.intToPtrMap)
    (inverse : machine.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (nonstrict : machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (allocLive : machine.memory.isAllocLive id = true)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global,.FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (info : AllocationInfo) (allocationInfo : machine.memory.getAllocInfo id = .ok info)
    (nonlive : info.kind ≠ .liveData)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance) (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes base)) 0 reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes base)) 0 reference).imm
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,reference⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (changedFrame frame localId adjusted valid borrowFrame id global.nextPointerTag)
        (nonliveMachine machine global fresh)) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes base)) 0 reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes base)) 0 reference).imm
  let copied := ConcreteEmptyReferenceArgumentCopy.copiedFrame frame localId value valid
  let afterFrame := TypedBorrowSteps.registeredFrame copied borrowFrame id global.nextPointerTag
  let afterMachine := nonliveMachine {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
    global fresh
  have result := WildcardNonliveReferenceArgumentCopy.copy_nonlive_argument options limits remaining span ctx debugOff cmp dynamicFuel validityFuel
    fuelEq validationEq id global base nonzero frames frame machine localId valid old
    live cached noClocks ghost shallow cachedAddress position positionValid ordered inverse nonstrict exposed allocLive borrowFrame frameBorrow enabled fresh info allocationInfo nonlive
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
end DuplicatePrefix.WildcardNonliveRootCopy
