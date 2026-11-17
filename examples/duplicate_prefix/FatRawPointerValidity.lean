import duplicate_prefix.RawPointerValidity
import duplicate_prefix.ReferenceValidity

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.FatRawPointerValidity
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open DuplicatePrefix.AllocationCopy DuplicatePrefix.ScalarCopyStage DuplicatePrefix.ReferenceValidity

private theorem visit_fat_raw_pointer
    (hooks : ValidityVisitor.Hooks Provenance S C E F A Pad) (choice : C) (fuel : Nat)
    (session : ValidityVisitor.Session Provenance) (place : RuntimePlace Provenance)
    (state : S) (pointee : TyId) (first second : Miri.Memory.Scalar Provenance)
    (target : MPlaceTy Provenance)
    (primitiveA primitiveB : Primitive) (rangeA rangeB : WrappingRange) (offset : Size)
    (repr : place.layout.layout.backendRepr = .ScalarPair
      (a := .Initialized (value := primitiveA) (validRange := rangeA))
      (b := .Initialized (value := primitiveB) (validRange := rangeB)) (bOffset := offset))
    (classification : hooks.classify choice place.layout.ty state = .ok (.rawPointer pointee false) state)
    (read : hooks.readImmediate choice place .rawPointer state = .ok ⟨.scalarPair first second, place.layout⟩ state)
    (write : hooks.writeNoValidate choice (.scalarPair first second) place state = .ok () state)
    (pointer : hooks.ptrToPlace choice ⟨.scalarPair first second, place.layout⟩ = pure target)
    (unsized : target.layout.layout.isSized = false)
    (metadata : source_check_metadata hooks choice target = pure ())
    (reset : session.flags.resetProvenanceAndPadding = true) (noRanges : session.dataBytes = none) :
    ValidityVisitor.visit hooks choice (fuel + 1) session place state = .ok session state := by
  unfold ValidityVisitor.visit
  unfold_internal ".ValidityVisitor.primitive"
  unfold_internal ".ValidityVisitor.resetPointer"
  unfold_internal ".ValidityVisitor.markPlace"
  simp [classification, read, reset, repr, write, noRanges, pointer, unsized, metadata,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

theorem validate_fat_raw_pointer_fields_shallow [DecidableEq K]
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (fuel : Nat) (choice : C)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : Miri.MIR.LocalId) (layout : LocalLayout) (first second : Miri.Memory.Scalar Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (.scalarPair first second)))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true)
    (primitiveA primitiveB : Primitive) (rangeA rangeB : WrappingRange) (offset : Size)
    (repr : layout.layout.backendRepr = .ScalarPair (a := .Initialized (value := primitiveA) (validRange := rangeA))
      (b := .Initialized (value := primitiveB) (validRange := rangeB)) (bOffset := offset))
    (debug : compiler.debugAssertions = false)
    (ghost : machine.user.payload.ghost = false)
    (retain : access.retainTouched = fun machine _ => machine)
    (name : String) (pointee : TyId) (target : MPlaceTy Provenance)
    (unsized : target.layout.layout.isSized = false)
    (targetQuery : hooks.ptrToPlace choice ⟨.scalarPair first second, layout⟩ = pure target)
    (metadataQuery : source_check_metadata hooks choice target = pure ())
    (nameQuery : hooks.typeName choice layout.ty = pure name)
    (kindQuery : hooks.classify choice layout.ty
      (Storage.withCurrent framesBefore frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}) =
      .ok (.rawPointer pointee false) (Storage.withCurrent framesBefore frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}))
    (toOpField : hooks.toOp = fun c place => placeToOp
      (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy compiler)) c place)
    (readField : hooks.readImmediate = fun c place expected => do
      let op ← placeToOp (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy compiler)) c place
      ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access) op expected)
    (noDebug : compiler.debugAbiCheck (.scalarPair first second) layout = pure ())
    (writeField : hooks.writeNoValidate = fun c value destination => do
      let validate ← ValidityMachine.enforceValidity
      ValidityMemory.writeNoValidate (ValidityMachine.memoryEnvironment access)
        (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy compiler))
        c (fun _ => validate) value destination)
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
  have toOp : hooks.toOp choice place active = .ok ⟨.immediate (.scalarPair first second), layout⟩ active := by
    rw [toOpField]
    exact place_to_op_ghost access allocation (ValidityMachine.compilerPolicy compiler) choice framesBefore frame
      activeMachine localId layout (.scalarPair first second) valid live cached sized debug rfl
  have read (expected : Miri.Memory.ExpectedValue) : hooks.readImmediate choice place expected active =
      .ok ⟨.scalarPair first second, layout⟩ active := by
    rw [readField]
    change (do
      let op ← placeToOp (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy compiler)) choice place
      ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access) op expected) active = _
    simp only [bind, EStateM.bind]
    rw [place_to_op_ghost access allocation (ValidityMachine.compilerPolicy compiler) choice framesBefore frame
      activeMachine localId layout (.scalarPair first second) valid live cached sized debug rfl]
    simp only
    exact ReferenceValidity.validity_read_pair access active layout first second primitiveA primitiveB rangeA rangeB offset repr retain expected
  have write : hooks.writeNoValidate choice (.scalarPair first second) place active = .ok () active := by
    rw [writeField]
    change (do
      let validate ← ValidityMachine.enforceValidity
      ValidityMemory.writeNoValidate (ValidityMachine.memoryEnvironment access)
        (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy compiler)) choice
        (fun _ => validate) (.scalarPair first second) place) active = _
    unfold ValidityMachine.enforceValidity
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
    exact ReferenceValidity.write_same_local_ghost access allocation (ValidityMachine.compilerPolicy compiler)
      choice framesBefore frame activeMachine localId (.scalarPair first second) layout
      valid live cached sized debug noDebug rfl _
  have classified : hooks.classify choice place.layout.ty active = .ok (.rawPointer pointee false) active := kindQuery
  have visit : ValidityVisitor.visit hooks choice (fuel + 1) initial place active = .ok initial active :=
    visit_fat_raw_pointer hooks choice fuel initial place active pointee first second target primitiveA primitiveB rangeA rangeB offset repr classified
      (read .rawPointer) write targetQuery unsized metadataQuery rfl rfl
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

open Lean Elab Command in
run_cmd do
  for declaration in [``visit_fat_raw_pointer, ``validate_fat_raw_pointer_fields_shallow] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.FatRawPointerValidity
