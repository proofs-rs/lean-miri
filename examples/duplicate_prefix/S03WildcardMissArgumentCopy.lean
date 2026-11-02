import duplicate_prefix.S03WildcardMissReference
import duplicate_prefix.ReferenceArgumentCopy
namespace DuplicatePrefix.S03WildcardMissArgumentCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ActualReferenceMetadata
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem copy_empty_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut = false)
    (implicitWrites : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (validationEq : options.limits.validation = validityFuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (old : Immediate Provenance) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (address : UInt64) (nonzero : address ≠ 0)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (miss : machine.user.addresses.allocIdFromAddr address 0
      (GlobalAddressLiveErrorExclusion.lookup machine.memory) = .ok none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
      ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm, reference⟩ view
      (Storage.withCurrent frames frame machine) = .ok ()
      (TypedRetagEmpty.afterTag (Storage.withCurrent frames {frame with locals := (frame.locals.set localId
        {value := .live (.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm),
         layout := frame.locals[localId].layout} valid)} machine) tracker fresh) := by
  let value := (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 reference).imm
  let postFrame := {frame with locals := (frame.locals.set localId
    {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)}
  have postValid : localId < postFrame.locals.size := by simpa only [postFrame, Array.size_set] using valid
  have postLive : postFrame.locals[localId].value = .live (.immediate value) := by simp [postFrame, valid]
  have postCached : postFrame.locals[localId].layout = some reference := by
    simpa only [postFrame, Array.getElem_set_self] using cached
  apply ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span debugOff frames frame machine localId old value
    valid live cached noClocks ghost shallow view destination
  rw [validationEq]
  exact S03WildcardMissReference.validate options remaining span cmp precise implicitWrites debugOff dynamicFuel validityFuel fuelEq
    frames postFrame machine localId postValid address nonzero postLive postCached ghost shallow tracker enabled mode fresh addressMode miss metadata notConstructed

end DuplicatePrefix.S03WildcardMissArgumentCopy
