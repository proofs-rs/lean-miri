import duplicate_prefix.CanonicalConfigFacts
import duplicate_prefix.LocalWrites

/-! The actual canonical local-write callback, specialized to the source-built
configuration while leaving the shallow validator's pointwise state fact as an
explicit composition premise. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace DuplicatePrefix.RootWriteCallback
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

/-- Exact actual `writeLocalImmediate` callback after a local place has selected
its local fast path. The validation getter is observed at the post-write state,
which is what the shallow validity visitor must establish. -/
theorem actual_local_write_callback
    [DecidableEq MiriMemoryKind]
    (options : Miri.Input.EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : LocalId) (old value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (sized : layout.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none)
    (validationAtPost : ValidityMachine.validationInProgress
      (Storage.withCurrent framesBefore
        {frame with locals := (frame.locals.set localId
          {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) =
      .ok false (Storage.withCurrent framesBefore
        {frame with locals := (frame.locals.set localId
          {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine)) :
    (PreparedContracts.actualConfig options () remaining span).projection.place.writeLocalImmediate
      () localId layout value (Storage.withCurrent framesBefore frame machine) =
    .ok () (Storage.withCurrent framesBefore
      {frame with locals := (frame.locals.set localId
        {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  change config.projection.place.writeLocalImmediate () localId layout value
    (Storage.withCurrent framesBefore frame machine) = _
  rw [fields.projectionWriteLocal]
  rw [fields.debugAbiNoChecks debugOff]
  exact LocalWrites.immediate_write_observed ValidityMachine.validationInProgress
    (fun _ _ => pure ()) framesBefore frame machine localId old value layout valid live
    sized noClocks validationAtPost (by rfl)

#print axioms actual_local_write_callback
end DuplicatePrefix.RootWriteCallback
