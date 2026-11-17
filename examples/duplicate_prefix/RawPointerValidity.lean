import duplicate_prefix.ScalarCopyStage

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

namespace DuplicatePrefix.RawPointerValidity
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open DuplicatePrefix.AllocationCopy DuplicatePrefix.ScalarCopyStage

theorem clear_nonpointer_local_ghost [DecidableEq K]
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : Miri.MIR.LocalId) (layout : LocalLayout) (value : Miri.Memory.Scalar Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (.scalar (value))))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true)
    (debug : compiler.debugAssertions = false)
    (ghost : machine.user.payload.ghost = true)
    (notPointer : value.isPointer = false) :
    ValidityMemory.clearPlaceProvenance (ValidityMachine.memoryEnvironment access)
      (ValidityMachine.placeHooks access allocation compiler) choice ValidityMachine.validationInProgress
      MachineHooks.afterLocalWrite (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout)
      (Storage.withCurrent framesBefore frame machine) = .ok () (Storage.withCurrent framesBefore frame machine) := by
  unfold ValidityMemory.clearPlaceProvenance
  simp only [bind, EStateM.bind]
  rw [place_to_op_ghost access allocation compiler choice framesBefore frame machine localId layout
    (.scalar (value)) valid live cached sized debug ghost]
  simp [Immediate.hasProvenance, notPointer, pure, EStateM.pure]

private theorem visit_thin_raw_pointer
    (hooks : ValidityVisitor.Hooks Provenance S C E F A Pad) (choice : C) (fuel : Nat)
    (session : ValidityVisitor.Session Provenance) (place : RuntimePlace Provenance)
    (state : S) (pointee : TyId) (value : Miri.Memory.Scalar Provenance)
    (primitive : Primitive) (range : WrappingRange)
    (repr : place.layout.layout.backendRepr = .Scalar (.Initialized (value := primitive) (validRange := range)))
    (classification : hooks.classify choice place.layout.ty state = .ok (.rawPointer pointee true) state)
    (read : hooks.readImmediate choice place .rawPointer state = .ok ⟨.scalar value, place.layout⟩ state)
    (clear : value.isPointer = false → hooks.clearProvenance choice place state = .ok () state)
    (reset : session.flags.resetProvenanceAndPadding = true) (noRanges : session.dataBytes = none) :
    ValidityVisitor.visit hooks choice (fuel + 1) session place state = .ok session state := by
  unfold ValidityVisitor.visit
  unfold_internal ".ValidityVisitor.primitive"
  unfold_internal ".ValidityVisitor.resetPointer"
  unfold_internal ".ValidityVisitor.scalarOf"
  unfold_internal ".ValidityVisitor.liftResult"
  unfold_internal ".ValidityVisitor.markPlace"
  cases pointing : value.isPointer
  · simp [classification, read, clear pointing, reset, noRanges, repr, pointing, Immediate.toScalar,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, Except.mapError]
  · simp [classification, read, reset, noRanges, repr, pointing, Immediate.toScalar,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, Except.mapError]

theorem validate_thin_raw_pointer_fields_shallow [DecidableEq K]
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (fuel : Nat) (choice : C)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : Miri.MIR.LocalId) (layout : LocalLayout) (value : Miri.Memory.Scalar Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (.scalar (value))))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true)
    (primitive : Primitive) (range : WrappingRange)
    (repr : layout.layout.backendRepr = .Scalar (.Initialized (value := primitive) (validRange := range)))
    (debug : compiler.debugAssertions = false)
    (ghost : machine.user.payload.ghost = false)
    (retain : access.retainTouched = fun machine _ => machine)
    (name : String) (pointee : TyId)
    (nameQuery : hooks.typeName choice layout.ty = pure name)
    (kindQuery : hooks.classify choice layout.ty
      (Storage.withCurrent framesBefore frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}) =
      .ok (.rawPointer pointee true) (Storage.withCurrent framesBefore frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}))
    (toOpField : hooks.toOp = fun c place => placeToOp
      (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy compiler)) c place)
    (readField : hooks.readImmediate = fun c place expected => do
      let op ← placeToOp (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy compiler)) c place
      ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access) op expected)
    (clearField : hooks.clearProvenance = fun c place => ValidityMemory.clearPlaceProvenance
      (ValidityMachine.memoryEnvironment access) (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy compiler))
      c ValidityMachine.validationInProgress MachineHooks.afterLocalWrite place)
    (withGhostField : hooks.withGhostValidation (A := ValidityVisitor.Session Provenance) =
      @ValidityMachine.withGhostValidation K U (ValidityVisitor.Session Provenance)) :
    ValidityVisitor.validatePlace hooks choice (fuel + 1)
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout) false true
      (Storage.withCurrent framesBefore frame machine) = .ok () (Storage.withCurrent framesBefore frame machine) := by
  let place := LocalPlaces.localRuntimePlace framesBefore.size frame localId layout
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent framesBefore frame activeMachine
  let initial : ValidityVisitor.Session Provenance := {
    path := ⟨name, #[]⟩, flags := ⟨true, false⟩, ctfeMode := none, refTracking := none, dataBytes := none }
  have toOp : hooks.toOp choice place active = .ok ⟨.immediate (.scalar (value)), layout⟩ active := by
    rw [toOpField]
    exact place_to_op_ghost access allocation (ValidityMachine.compilerPolicy compiler) choice framesBefore frame
      activeMachine localId layout (.scalar (value)) valid live cached sized debug rfl
  have read (expected : Miri.Memory.ExpectedValue) : hooks.readImmediate choice place expected active =
      .ok ⟨.scalar (value), layout⟩ active := by
    rw [readField]
    change (do
      let op ← placeToOp (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy compiler)) choice place
      ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access) op expected) active = _
    simp only [bind, EStateM.bind]
    rw [place_to_op_ghost access allocation (ValidityMachine.compilerPolicy compiler) choice framesBefore frame
      activeMachine localId layout (.scalar (value)) valid live cached sized debug rfl]
    simp only
    exact validity_read_scalar access active layout (value) primitive range repr retain expected
  have clear (notPointer : value.isPointer = false) : hooks.clearProvenance choice place active = .ok () active := by
    rw [clearField]
    exact clear_nonpointer_local_ghost access allocation (ValidityMachine.compilerPolicy compiler) choice framesBefore frame
      activeMachine localId layout value valid live cached sized debug rfl notPointer
  have classified : hooks.classify choice place.layout.ty active = .ok (.rawPointer pointee true) active := kindQuery
  have visit : ValidityVisitor.visit hooks choice (fuel + 1) initial place active = .ok initial active :=
    visit_thin_raw_pointer hooks choice fuel initial place active pointee value primitive range repr classified
      (read .rawPointer) clear rfl rfl
  have named : hooks.typeName choice place.layout.ty = pure name := nameQuery
  change ValidityVisitor.validatePlace hooks choice (fuel + 1) place false true _ = _
  unfold ValidityVisitor.validatePlace
  rw [named]
  simp only [bind, EStateM.bind, pure, EStateM.pure, Bool.false_eq_true, ↓reduceIte]
  rw [withGhostField]
  unfold ValidityMachine.withGhostValidation
  simp only [Storage.withCurrent, ghost, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, EStateM.bind]
  erw [toOp]
  simp only [bind, EStateM.bind]
  erw [visit]
  simp only [bind, EStateM.bind]
  unfold_internal ".ValidityVisitor.resetPadding"
  simp only [initial, bind, EStateM.bind, pure, EStateM.pure]
  simp only [active, activeMachine, Storage.withCurrent, ↓reduceIte]
  have restored : {machine.user.payload with ghost := false} = machine.user.payload := by rw [← ghost]
  simp only [restored]


#print axioms validate_thin_raw_pointer_fields_shallow
open Lean Elab Command in
run_cmd do
  for declaration in [``clear_nonpointer_local_ghost, ``visit_thin_raw_pointer, ``validate_thin_raw_pointer_fields_shallow] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.RawPointerValidity
