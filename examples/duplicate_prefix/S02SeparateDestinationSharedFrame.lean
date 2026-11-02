import duplicate_prefix.S02SeparateDestinationRejectedEntryPrefix
import duplicate_prefix.PositiveRootInstalledFrame

namespace DuplicatePrefix.S02SeparateDestinationSharedFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Structural facts at the actual shared-Ref statement from the positive
installed frame and the executed pure-prefix Shape. -/
theorem of_shape
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (race : before.dataRace = none)
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (count : UInt64) (destinationId : AllocId) (destinationTag : BorTag)
    (entry frame : CompilerFrameContext.ActualFrame)
    (installed : entry = PositiveRootInstalledFrame.installed
      (RawRootInvocation.root before place race)
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
      count {} reference.id reference.tracker.global.nextPointerTag destinationId destinationTag)
    (shape : GenericFunctionEntryPrefix.Shape entry frame count) :
    frame.body = RootBody.reflected.body.body ∧
    frame.bodyIdentity = RootBody.reflected.body.identity ∧
    frame.functionInstance = RootBody.reflected.functionInstance ∧
    frame.location = .mir ⟨2,11⟩ ∧ frame.locals.size = 25 ∧
    frame.extra.dataRace = none ∧
    frame.locals[1]? = some ⟨.live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm),
      some ActualReferenceMetadata.reference⟩ ∧
    frame.locals[11]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    frame.locals[12]? = some ⟨.live (.immediate .uninit),none⟩ ∧
    CopyHelperCleanup.AllImmediate frame := by
  let root := RawRootInvocation.root before place race
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  have metadata := PositiveRootInstalledFrame.metadata root adjusted count {} reference.id
    reference.tracker.global.nextPointerTag destinationId destinationTag
  have slot := PositiveRootInstalledFrame.slot_option root (RawRootInvocation.locals before place race)
    adjusted count {} reference.id reference.tracker.global.nextPointerTag destinationId destinationTag ⟨1,by decide⟩
  refine ⟨?_,?_,?_,shape.location,shape.size,?_,?_,shape.slot11,shape.slot12,shape.immediate⟩
  · rw [shape.body,installed,metadata.1]
    exact root.body
  · rw [shape.identity,installed,metadata.2.1]
    exact root.identity
  · rw [shape.callee,installed,metadata.2.2.1]
    exact root.callee
  · rw [shape.extra,installed,metadata.2.2.2.2.2.2.1]
    exact root.noClocks
  · rw [shape.slot1,installed]
    simpa [root,adjusted] using slot

end
end DuplicatePrefix.S02SeparateDestinationSharedFrame

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationSharedFrame.of_shape) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate shared-frame dependency {dependency}"
