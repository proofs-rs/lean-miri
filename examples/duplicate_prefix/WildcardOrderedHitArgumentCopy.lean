import duplicate_prefix.ActualWildcardOrderedHitReference
import duplicate_prefix.ConcreteEmptyReferenceArgumentCopy
namespace DuplicatePrefix.WildcardOrderedHitArgumentCopy
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem copy (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (validationEq : options.limits.validation = validityFuel + 1)
    (id : AllocId) (global : GlobalState)
    (base : UInt64) (nonzero : base ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
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
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (inverse : WildcardGeneralHitReborrow.Geometry machine.user.addresses.intToPtrMap base base id entry.allocation.byteSize)
    (exposed : machine.user.addresses.exposed.contains id = true)
    (tagMapFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping global.nextPointerTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes base)) 0 reference).imm
    let postFrame := ConcreteEmptyReferenceArgumentCopy.copiedFrame frame localId value valid
    let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
    let afterFrame := TypedBorrowSteps.registeredFrame postFrame borrowFrame id global.nextPointerTag
    let afterMachine := (ActualWildcardOrderedHitReference.resultState frames postFrame activeMachine borrowFrame global fresh id entry).machine
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
      ⟨.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes base)) 0 reference).imm, reference⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {afterFrame with locals := (afterFrame.locals.set localId
          {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes base)) 0 reference).imm),
           layout := (afterFrame.locals[localId]'(by simpa [afterFrame,postFrame,ConcreteEmptyReferenceArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow] using valid)).layout}
          (by simpa [afterFrame,postFrame,ConcreteEmptyReferenceArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow] using valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes base)) 0 reference).imm
  let postFrame := ConcreteEmptyReferenceArgumentCopy.copiedFrame frame localId value valid
  have postValid : localId < postFrame.locals.size := by simpa only [postFrame, ConcreteEmptyReferenceArgumentCopy.copiedFrame, Array.size_set] using valid
  have postLive : postFrame.locals[localId].value = .live (.immediate value) := by simp [postFrame, ConcreteEmptyReferenceArgumentCopy.copiedFrame]
  have postCached : postFrame.locals[localId].layout = some reference := by
    simpa only [postFrame, ConcreteEmptyReferenceArgumentCopy.copiedFrame, Array.getElem_set_self] using cached
  have checked := ActualWildcardOrderedHitReference.validate_runtime options remaining span ctx debugOff cmp dynamicFuel validityFuel
    fuelEq id global base nonzero entry frames postFrame machine localId postValid postLive postCached ghost shallow
    cachedAddress present borrowFrame frameBorrow enabled fresh addressMode inverse exposed tagMapFresh noFree fits metadata notConstructed
  apply ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span debugOff frames frame machine
    localId old value valid live cached noClocks ghost shallow view destination _
  rw [validationEq]
  exact checked

end DuplicatePrefix.WildcardOrderedHitArgumentCopy
