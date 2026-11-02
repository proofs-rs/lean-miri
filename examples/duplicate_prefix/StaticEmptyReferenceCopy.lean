import duplicate_prefix.StaticEmptyReferenceValidity
import duplicate_prefix.ConcreteEmptyReferenceArgumentCopy

namespace DuplicatePrefix.StaticEmptyReferenceCopy
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

theorem copy_argument (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (limits : ExecutionMachine.Limits)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (global : GlobalState)
    (base offset : UInt64) (nonzero : base + offset ≠ 0)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (noClocks : frame.extra.dataRace = none)
    (cached : frame.locals[localId].layout = some reference)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some ⟨global, .FnEntry⟩)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (distinct : parentTag ≠ global.nextPointerTag)
    (source : Allocation CtfeProvenance Unit) (definition : Nat)
    (initializer : PreparedReflection.actual.image.initializers.find? (·.1 == definition) = some (definition,source))
    (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      machine.memory global.rootPointerTags machine.user.addresses.baseAddr)
    (rootCached : global.rootTag? id = some parentTag)
    (race : machine.dataRace = none)
    (noExtras : (machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (absent : machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : machine.memory.hasFunctionPointer id = false)
    (noVaList : machine.memory.hasVaListId id = false)
    (descriptor : machine.memory.findGlobal? id = some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference)
    : ∃ converted : Allocation Provenance Unit,
      GlobalAllocationAttributes.Attributes source converted ∧
      let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference).imm
      let postFrame := ConcreteEmptyReferenceArgumentCopy.copiedFrame frame localId value valid
      let afterFrame := TypedBorrowSteps.registeredFrame postFrame borrowFrame id global.nextPointerTag
      let afterMachine := (StaticEmptyReferencePointer.resultState options frames postFrame borrowFrame
        {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
        ⟨global,.FnEntry⟩ fresh id parentTag source converted).machine
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,reference⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {afterFrame with locals := (afterFrame.locals.set localId
          {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) 0 reference).imm),
           layout := (afterFrame.locals[localId]'(by simpa [afterFrame,postFrame,ConcreteEmptyReferenceArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow] using valid)).layout}
          (by simpa [afterFrame,postFrame,ConcreteEmptyReferenceArgumentCopy.copiedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow] using valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 reference).imm
  let postFrame := ConcreteEmptyReferenceArgumentCopy.copiedFrame frame localId value valid
  have postValid : localId < postFrame.locals.size := by
    simpa only [postFrame,ConcreteEmptyReferenceArgumentCopy.copiedFrame,Array.size_set] using valid
  have postLive : postFrame.locals[localId].value = .live (.immediate value) := by
    simp [postFrame,ConcreteEmptyReferenceArgumentCopy.copiedFrame,valid]
  have postCached : postFrame.locals[localId].layout = some reference := by
    simpa only [postFrame,ConcreteEmptyReferenceArgumentCopy.copiedFrame,Array.getElem_set_self] using cached
  obtain ⟨converted,facts,checked⟩ := StaticEmptyReferenceValidity.validate_runtime_global options remaining span ctx
    actualPointers debugOff cmp dynamicFuel validityFuel fuelEq id parentTag global base offset nonzero
    frames postFrame machine localId postValid postLive postCached ghost shallow cachedAddress borrowFrame
    frameBorrow enabled fresh distinct source definition initializer supported rootCached race noExtras absent noFunction noVaList descriptor
    metadata notConstructed
  refine ⟨converted,facts,?_⟩
  apply ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span debugOff frames frame machine
    localId old value valid live cached noClocks ghost shallow view destination _
  rw [validationEq]
  exact checked

end
end DuplicatePrefix.StaticEmptyReferenceCopy

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.StaticEmptyReferenceCopy.copy_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved global supported reference copy dependency {dependency}"
