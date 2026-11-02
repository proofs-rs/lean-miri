import duplicate_prefix.LenEntryValidity
import duplicate_prefix.ReferenceArgumentCopy
namespace DuplicatePrefix.LenArgumentCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem shared_no_padding : CompilerCopy.hasPadding PreparedReflection.actual.compiler.runtime false SharedReferenceMetadata.sharedLayout = .ok false := by
  with_unfolding_all rfl
theorem shared_sized : SharedReferenceMetadata.sharedLayout.layout.isSized = true := by decide +kernel

theorem copy_with_nested_validation
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (old value : Immediate Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some SharedReferenceMetadata.sharedLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId SharedReferenceMetadata.sharedLayout)
    (after : CanonicalConfigFacts.RootState)
    (validated : ValidityMachine.validateRuntime
      (PreparedContracts.actualConfig options () remaining span).validity () options.limits.validation
      (LocalPlaces.localRuntimePlace frames.size frame localId SharedReferenceMetadata.sharedLayout) true
      (Storage.withCurrent frames {frame with locals := (frame.locals.set localId
        {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) =
      .ok () after) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
      ⟨.immediate value, SharedReferenceMetadata.sharedLayout⟩ view (Storage.withCurrent frames frame machine) = .ok () after := by
  let cfg := PreparedContracts.actualConfig options () (remaining + 1) span
  let bound := ExecutionMachine.withValidation cfg limits
  let place := (ExecutionMachine.projectionHooks bound).place
  let dest := LocalPlaces.localRuntimePlace frames.size frame localId SharedReferenceMetadata.sharedLayout
  let postFrame := {frame with locals := (frame.locals.set localId
    {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)}
  let postState := Storage.withCurrent frames postFrame machine
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have compatible : bound.copy.compatible = CompilerCovariance.compatible PreparedReflection.actual.compiler false := by
    change cfg.copy.compatible = _
    rw [fields.copyCompatible, debugOff]
  have flag := GenericCallReturn.same_layout_transmute_flag place bound.copy PreparedReflection.actual.compiler ()
    SharedReferenceMetadata.sharedLayout value dest rfl compatible
  have exactCopy : copyRuntimePlace place bound.copy () ⟨.immediate value, SharedReferenceMetadata.sharedLayout⟩ dest true =
      (ExecutionMachine.rvalueHooks cfg limits).copyOp () ⟨.immediate value, SharedReferenceMetadata.sharedLayout⟩ dest := by
    rw [flag]; rfl
  have copy := ActualScalarCopy.actual_copy_no_padding options limits (remaining + 1) span debugOff
    SharedReferenceMetadata.sharedLayout value dest rfl shared_no_padding shared_sized
  have physical := RootUsizeWrite.write_local_no_validate options limits (remaining + 1) span debugOff
    frames frame machine localId old value SharedReferenceMetadata.sharedLayout valid live shared_sized noClocks ghost
  have enforced : place.enforceValidity () SharedReferenceMetadata.sharedLayout postState = .ok true postState := by
    change cfg.projection.place.enforceValidity () SharedReferenceMetadata.sharedLayout postState = _
    rw [fields.projectionEnforce]
    simp [ValidityMachine.enforceValidity, postState, Storage.withCurrent, shallow,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have validation : place.validate () dest postState = .ok () after := by
    change cfg.projection.place.validate () dest postState = _
    rw [fields.projectionValidate, CanonicalConfigFacts.actual_validate_successor]
    exact validated
  change copyRuntimePlace place bound.copy () ⟨.immediate value, SharedReferenceMetadata.sharedLayout⟩ view.toRuntimePlace true _ = _
  rw [destination, exactCopy, copy]
  change writePlaceImmediate place () value dest _ = _
  unfold writePlaceImmediate
  simp only [bind, EStateM.bind]
  rw [physical]
  simp only [bind, EStateM.bind]
  erw [enforced]
  exact validation


def copiedFrame (frame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId)
    (value : Immediate Provenance) (valid : localId < frame.locals.size) :=
  {frame with locals := (frame.locals.set localId
    {value := .live (.immediate value),layout := frame.locals[localId].layout} valid)}

theorem copy_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capacity base offset len : UInt64)
    (tree : entry.allocation.extra = tree3 tags
      (partitionWithInside capacity offset (offset+len) rootLocation (location3 false)))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 3 false)
    (nextTag : tracker.global.nextPointerTag = tags 3)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some SharedReferenceMetadata.sharedLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId SharedReferenceMetadata.sharedLayout) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let copied := copiedFrame frame localId value valid
    let finalTree := tree4 tags (partitionWithInside capacity offset (offset+len) rootLocation (location4 false))
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,SharedReferenceMetadata.sharedLayout⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {(TypedBorrowSteps.registeredFrame copied borrowFrame id tracker.global.nextPointerTag) with
          locals := copied.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm),
             layout := (copied.locals[localId]'(by simpa only [copied,copiedFrame,Array.size_set] using valid)).layout}
            (by simpa only [copied,copiedFrame,Array.size_set] using valid)} resultMachine) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
  let copied := copiedFrame frame localId value valid
  have postValid : localId < copied.locals.size := by simpa only [copied,copiedFrame,Array.size_set] using valid
  have postLive : copied.locals[localId].value = .live (.immediate value) := by simp [copied,copiedFrame]
  have postCached : copied.locals[localId].layout = some SharedReferenceMetadata.sharedLayout := by
    simpa only [copied,copiedFrame,Array.getElem_set_self] using cached
  have checked := LenEntryValidity.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    tags distinct id entry capacity base offset len tree allocationSize positive nonzero signedFits bounds frames copied machine
    tracker enabled mode borrowFrame frameBorrow mask nextTag fresh localId postValid postLive postCached ghost shallow
    cachedAddress present race metadata notConstructed
  apply copy_with_nested_validation options limits remaining span debugOff frames frame machine
    localId old value valid live cached noClocks ghost shallow view destination _
  rw [validationEq]
  exact checked

#print axioms copy_argument
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``copy_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved asmut argument dependency {dependency}"
end
end DuplicatePrefix.LenArgumentCopy
