import duplicate_prefix.LocalWrites

/-! Actual optimized-local write behavior when a shallow/reference validation
scope is already active. -/
namespace DuplicatePrefix.ReferenceLocalWrites
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

/-- During validation the local write still changes the frame, while the
source `afterLocalWrite` hook is skipped by the active validation flag. -/
theorem immediate_write_validation_active
    (validation : MachineHooks.M K User Bool)
    (debugAbiCheck : Immediate Provenance → LocalLayout → MachineHooks.M K User Unit)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (localId : LocalId)
    (old value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (sized : layout.layout.isSized = true)
    (validationTrue : validation (Storage.withCurrent framesBefore
      {frame with locals := (frame.locals.set localId
        {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) =
      .ok true (Storage.withCurrent framesBefore
        {frame with locals := (frame.locals.set localId
          {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine))
    (noDebug : debugAbiCheck value layout = pure ()) :
    placeWriteLocalImmediate MachineHooks.currentFrame MachineHooks.setCurrentFrame
      validation MachineHooks.afterLocalWrite debugAbiCheck localId layout value
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore
        {frame with locals := (frame.locals.set localId
          {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) := by
  simp_local_write

#print axioms immediate_write_validation_active
end DuplicatePrefix.ReferenceLocalWrites
