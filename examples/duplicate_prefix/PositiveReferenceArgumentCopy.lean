import duplicate_prefix.ReferenceArgumentCopy
import duplicate_prefix.ActualPositiveReference
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PositiveReferenceArgumentCopy
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Input Miri.Interpreter
open Miri.TreeBorrows CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
noncomputable section

def copiedFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (localId : MIR.LocalId)
    (value : Immediate Provenance) (valid : localId < frame.locals.size) :=
  {frame with locals := (frame.locals.set localId
    {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)}

theorem copy_positive_argument (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel + 1)
    (validationEq : options.limits.validation = validityFuel + 1)
    (id : AllocId) (parentTag : BorTag) (global : GlobalState)
    (base offset len capacity : UInt64) (nonzero : base + offset ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounded : len ≤ 9223372036854775807)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
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
    (distinct : parentTag ≠ global.nextPointerTag)
    (rootUnprotected : global.protectedTags.contains parentTag = false)
    (root : entry.allocation.extra = BorrowTree.new parentTag (Size.ofBytes capacity))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata =
      PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any
      (·.value.ty == 4) = false)
    (afterFrame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (afterMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sameLocals : afterFrame.locals = (copiedFrame frame localId (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))) len reference).imm valid).locals)
    (sameDestination : LocalPlaces.localRuntimePlace frames.size frame localId reference =
      LocalPlaces.localRuntimePlace frames.size afterFrame localId reference)
    (ghostAfter : afterMachine.user.payload.ghost = true)
    (afterState : TypedRetagGeneric.completedState
      (Storage.withCurrent frames (copiedFrame frame localId (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))) len reference).imm valid) {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}})
      frames (copiedFrame frame localId (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))) len reference).imm valid) borrowFrame id entry parentTag global fresh capacity offset len =
      Storage.withCurrent frames afterFrame afterMachine)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId reference) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
      ⟨.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))) len reference).imm, reference⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {afterFrame with locals := (afterFrame.locals.set localId
          {value := .live (.immediate (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) len reference).imm),
           layout := (afterFrame.locals[localId]'(by simpa [sameLocals, copiedFrame] using valid)).layout}
          (by simpa [sameLocals, copiedFrame] using valid))}
        {afterMachine with user := {afterMachine.user with payload := {afterMachine.user.payload with ghost := false}}}) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base + offset))) len reference).imm
  let postFrame := copiedFrame frame localId value valid
  have postValid : localId < postFrame.locals.size := by simpa only [postFrame, copiedFrame, Array.size_set] using valid
  have postLive : postFrame.locals[localId].value = .live (.immediate value) := by
    simp [postFrame, copiedFrame, valid]
  have postCached : postFrame.locals[localId].layout = some reference := by
    simpa only [postFrame, copiedFrame, Array.getElem_set_self] using cached
  have checked := ActualPositiveReference.validate_runtime_positive options remaining span ctx debugOff cmp
    dynamicFuel validityFuel fuelEq id parentTag global base offset len capacity nonzero entry positive signedFits
    bounded bounds frames postFrame machine localId postValid postLive postCached ghost shallow cachedAddress present
    borrowFrame frameBorrow enabled fresh distinct rootUnprotected root allocationSize race metadata notConstructed
    afterFrame afterMachine sameLocals sameDestination ghostAfter afterState
  apply ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span debugOff frames frame machine
    localId old value valid live cached noClocks ghost shallow view destination _
  rw [validationEq]
  exact checked

#print axioms copy_positive_argument
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``copy_positive_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved positive argument dependency {dependency}"
end
end DuplicatePrefix.PositiveReferenceArgumentCopy
