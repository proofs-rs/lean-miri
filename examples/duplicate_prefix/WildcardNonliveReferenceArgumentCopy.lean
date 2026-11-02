import duplicate_prefix.ActualWildcardNonliveReference
import duplicate_prefix.ConcreteEmptyReferenceArgumentCopy
namespace DuplicatePrefix.WildcardNonliveReferenceArgumentCopy
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
open ConcreteEmptyReferenceArgumentCopy ActualConcreteEmptyReference
theorem copy_nonlive_argument (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (validationEq : options.limits.validation = validityFuel + 1)
    (id : AllocId) (global : GlobalState)
    (base : UInt64) (nonzero : base ≠ 0)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (position : Nat) (positionValid : position < machine.user.addresses.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered machine.user.addresses.intToPtrMap)
    (inverse : machine.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (nonstrict : machine.user.addresses.provenanceMode ≠ .strict)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (allocLive : machine.memory.isAllocLive id = true)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (info : AllocationInfo)
    (allocationInfo : machine.memory.getAllocInfo id = .ok info)
    (nonlive : info.kind ≠ .liveData)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 4) = false)
    (afterFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (afterMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sameLocals : afterFrame.locals = (copiedFrame frame localId (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes base)) 0 reference).imm valid).locals)
    (sameDestination : LocalPlaces.localRuntimePlace frames.size frame localId reference =
      LocalPlaces.localRuntimePlace frames.size afterFrame localId reference)
    (ghostAfter : afterMachine.user.payload.ghost = true)
    (afterState : nonliveRetagState frames (copiedFrame frame localId (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes base)) 0 reference).imm valid) machine borrowFrame global fresh id =
      Storage.withCurrent frames afterFrame afterMachine)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
      ⟨.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes base)) 0 reference).imm, reference⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {afterFrame with locals := (afterFrame.locals.set localId
          {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes base)) 0 reference).imm),
           layout := (afterFrame.locals[localId]'(by simpa [sameLocals, copiedFrame] using valid)).layout}
          (by simpa [sameLocals, copiedFrame] using valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes base)) 0 reference).imm
  let postFrame := copiedFrame frame localId value valid
  have postValid : localId < postFrame.locals.size := by simpa only [postFrame, copiedFrame, Array.size_set] using valid
  have postLive : postFrame.locals[localId].value = .live (.immediate value) := by simp [postFrame, copiedFrame, valid]
  have postCached : postFrame.locals[localId].layout = some reference := by
    simpa only [postFrame, copiedFrame, Array.getElem_set_self] using cached
  have checked := ActualWildcardNonliveReference.validate_runtime_nonlive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq id global base nonzero frames postFrame machine localId postValid postLive postCached ghost shallow cachedAddress position positionValid ordered inverse nonstrict exposed allocLive borrowFrame frameBorrow enabled fresh info allocationInfo nonlive metadata notConstructed afterFrame afterMachine sameLocals sameDestination ghostAfter afterState
  apply ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span debugOff frames frame machine
    localId old value valid live cached noClocks ghost shallow view destination _
  rw [validationEq]
  exact checked

end
end DuplicatePrefix.WildcardNonliveReferenceArgumentCopy
