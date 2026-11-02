import duplicate_prefix.ScalarCopyStage
import duplicate_prefix.ReferenceLocalWrites
import duplicate_prefix.ReferenceChecks
import duplicate_prefix.TypedRetagGeneric

/-! Source shallow validity traversal for a local slice reference. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.ReferenceValidity
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open Lean Elab

private def sourceName (suffix : String) : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected exact reference validity helper {suffix}"
elab "source_check_metadata" : term => return mkConst (← sourceName ".ValidityVisitor.checkMetadata")
elab "source_check_safe" : term => return mkConst (← sourceName ".ValidityVisitor.checkSafe")

def referenceSession (name : String) : ValidityVisitor.Session Provenance :=
  {path := ⟨name, #[]⟩, flags := ⟨true, false⟩, ctfeMode := none, refTracking := none, dataBytes := none}

theorem metadata_slice {S C E F A Pad : Type}
    (hooks : ValidityVisitor.Hooks Provenance S C E F A Pad) (choice : C)
    (place : MPlaceTy Provenance) (len : UInt64)
    (tail : hooks.metadataTail choice place.layout.ty = pure .sliceOrStr)
    (metadata : place.mplace.metadata = .metadata (Scalar.fromScalarInt (ScalarInt.ofUInt64 len)))
    (width : hooks.target.pointerSize = Size.ofBytes 8) :
    source_check_metadata hooks choice place = pure () := by
  funext state
  unfold_typed ".ValidityVisitor.checkMetadata"
  simp only [tail, bind, EStateM.bind, pure, EStateM.pure]
  unfold_typed ".ValidityVisitor.liftResult"
  simp only [metadata, MemPlaceMeta.unwrapMeta, width, CopyIntrinsic.usize_scalar_roundtrip,
    Except.mapError, bind, EStateM.bind, pure, EStateM.pure]

theorem validity_read_pair {K U : Type} [DecidableEq K]
    (access : ValidityMachine.Access K U) (state : ValidityMachine.State K U)
    (layout : LocalLayout) (first second : Miri.Memory.Scalar Provenance)
    (primitiveA primitiveB : Primitive) (rangeA rangeB : WrappingRange) (offset : Size)
    (repr : layout.layout.backendRepr =
      .ScalarPair (a := .Initialized (value := primitiveA) (validRange := rangeA))
        (b := .Initialized (value := primitiveB) (validRange := rangeB)) (bOffset := offset))
    (retain : access.retainTouched = fun machine _ => machine) (expected : ExpectedValue) :
    ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access)
      ⟨.immediate (.scalarPair first second), layout⟩ expected state =
      .ok ⟨.scalarPair first second, layout⟩ state := by
  unfold ValidityMemory.readImmediate Miri.Interpreter.readImmediate
  unfold_internal ".Miri.Interpreter.isPrimitiveReadable"
  unfold_internal ".ValidityMemory.commit"
  simp [ValidityMachine.memoryEnvironment, localMemoryLayout, repr,
    Miri.Interpreter.readImmediateRaw, retain, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    pure, Pure.pure, EStateM.pure, Except.pure, Except.bind, Except.mapError, Id.run, Id.instMonad]

#print axioms validity_read_pair

theorem read_local_pair_ghost {K U C : Type} [DecidableEq K]
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (localId : Miri.MIR.LocalId)
    (layout : LocalLayout) (first second : Scalar Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (.scalarPair first second)))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true) (debug : compiler.debugAssertions = false)
    (ghost : machine.user.payload.ghost = true)
    (primitiveA primitiveB : Primitive) (rangeA rangeB : WrappingRange) (offset : Size)
    (repr : layout.layout.backendRepr = .ScalarPair
      (a := .Initialized (value := primitiveA) (validRange := rangeA))
      (b := .Initialized (value := primitiveB) (validRange := rangeB)) (bOffset := offset))
    (retain : access.retainTouched = fun machine _ => machine) (expected : ExpectedValue) :
    (do
      let op ← placeToOp (ValidityMachine.placeHooks access allocation compiler) choice
        (LocalPlaces.localRuntimePlace frames.size frame localId layout)
      ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access) op expected)
      (Storage.withCurrent frames frame machine) =
      .ok ⟨.scalarPair first second, layout⟩ (Storage.withCurrent frames frame machine) := by
  simp only [bind, EStateM.bind]
  rw [ScalarCopyStage.place_to_op_ghost access allocation compiler choice frames frame machine localId
    layout (.scalarPair first second) valid live cached sized debug ghost]
  exact validity_read_pair access _ layout first second primitiveA primitiveB rangeA rangeB offset repr retain expected

#print axioms read_local_pair_ghost

theorem write_local_ghost {K U C : Type} [DecidableEq K]
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (localId : Miri.MIR.LocalId)
    (old value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true)
    (debug : compiler.debugAssertions = false)
    (noDebug : compiler.debugAbiCheck value layout = pure ())
    (ghost : machine.user.payload.ghost = true) (willValidate : MemoryOperandLayout → Bool) :
    ValidityMemory.writeNoValidate (ValidityMachine.memoryEnvironment access)
      (ValidityMachine.placeHooks access allocation compiler) choice willValidate value
      (LocalPlaces.localRuntimePlace frames.size frame localId layout)
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {frame with locals := (frame.locals.set localId
          {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) := by
  have write := ReferenceLocalWrites.immediate_write_validation_active
    ValidityMachine.validationInProgress compiler.debugAbiCheck frames frame machine localId
    old value layout valid live sized
    (by simp [ValidityMachine.validationInProgress, Storage.withCurrent, ghost,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]) noDebug
  unfold ValidityMemory.writeNoValidate
  simp only [LocalPlaces.localRuntimePlace]
  simp only [ValidityMachine.placeHooks, ValidityMachine.compilerPolicy]
  simp_local_place

#print axioms write_local_ghost

theorem write_same_local_ghost {K U C : Type} [DecidableEq K]
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (localId : Miri.MIR.LocalId)
    (value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate value))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true) (debug : compiler.debugAssertions = false)
    (noDebug : compiler.debugAbiCheck value layout = pure ())
    (ghost : machine.user.payload.ghost = true) (willValidate : MemoryOperandLayout → Bool) :
    ValidityMemory.writeNoValidate (ValidityMachine.memoryEnvironment access)
      (ValidityMachine.placeHooks access allocation compiler) choice willValidate value
      (LocalPlaces.localRuntimePlace frames.size frame localId layout)
      (Storage.withCurrent frames frame machine) = .ok () (Storage.withCurrent frames frame machine) := by
  have result := write_local_ghost access allocation compiler choice frames frame machine localId
    value value layout valid live cached sized debug noDebug ghost willValidate
  have sameEntry : {value := .live (.immediate value), layout := frame.locals[localId].layout} =
      frame.locals[localId] := by rw [← live]
  rw [sameEntry, Array.set_getElem_self] at result
  exact result

#print axioms write_same_local_ghost

theorem check_reference_stage {S C E F A Pad : Type}
    (hooks : ValidityVisitor.Hooks Provenance S C E F A Pad) (choice : C)
    (name : String) (destination : RuntimePlace Provenance) (input adjusted : RvalueImmTy Provenance)
    (place : MPlaceTy Provenance) (size : Size) (align : Align) (scalar : Scalar Provenance)
    (before afterRetag afterWrite : S)
    (read : hooks.readImmediate choice destination .reference before = .ok input before)
    (construct : hooks.ptrToPlace choice input = pure place)
    (unsized : place.layout.layout.isSized = false)
    (metadata : source_check_metadata hooks choice place = pure ())
    (dynamic : hooks.sizeAndAlign choice place = pure (some (size, align)))
    (checked : hooks.checkPointerAccess choice place.mplace.ptr size before = .ok (.ok ()) before)
    (retag : hooks.retagPointer choice input destination.layout.ty before = .ok (some adjusted) afterRetag)
    (write : hooks.writeNoValidate choice adjusted.imm destination afterRetag = .ok () afterWrite)
    (encoded : Scalar.fromMaybePointer hooks.target.base place.mplace.ptr = .ok scalar)
    (nonnull : hooks.scalarMayBeNull choice scalar = pure false)
    (inhabited : hooks.opsemInhabited choice place.layout.ty = pure true)
    (aligned : hooks.checkPointerAlignResult choice place.mplace.ptr align afterWrite = .ok (.ok ()) afterWrite) :
    source_check_safe hooks choice (referenceSession name) destination destination.layout.ty (.reference true) before =
      .ok (referenceSession name) afterWrite := by
  unfold_typed ".ValidityVisitor.checkSafe"
  simp only [read, bind, EStateM.bind, pure, EStateM.pure, referenceSession]
  unfold_typed ".ValidityVisitor.markPlace"
  simp only [Option.isNone_none, Bool.true_eq, ↓reduceIte,
    bind, EStateM.bind, pure, EStateM.pure, construct]
  simp only [unsized, Bool.not_false, Bool.true_eq, ↓reduceIte, metadata, dynamic,
    bind, EStateM.bind, pure, EStateM.pure, Option.getD_some, checked]
  unfold ValidityVisitor.retagSafePointer ValidityVisitor.mapRetagOutcome
  simp only [retag, bind, EStateM.bind, pure, EStateM.pure, write]
  unfold_typed ".ValidityVisitor.liftResult"
  simp only [encoded, Except.mapError, nonnull, inhabited,
    bind, EStateM.bind, pure, EStateM.pure, Bool.false_eq_true, Bool.not_true, ↓reduceIte]
  unfold ValidityVisitor.mapPointerAlignmentOutcome
  simp only [aligned, bind, EStateM.bind, pure, EStateM.pure]

theorem check_reference_stage_at {S C E F A Pad : Type}
    (hooks : ValidityVisitor.Hooks Provenance S C E F A Pad) (choice : C)
    (name : String) (destination : RuntimePlace Provenance) (input adjusted : RvalueImmTy Provenance)
    (place : MPlaceTy Provenance) (size : Size) (align : Align) (scalar : Scalar Provenance)
    (before afterRetag afterWrite : S)
    (read : hooks.readImmediate choice destination .reference before = .ok input before)
    (construct : hooks.ptrToPlace choice input = pure place)
    (unsized : place.layout.layout.isSized = false)
    (metadata : source_check_metadata hooks choice place = pure ())
    (dynamic : hooks.sizeAndAlign choice place before = .ok (some (size, align)) before)
    (checked : hooks.checkPointerAccess choice place.mplace.ptr size before = .ok (.ok ()) before)
    (retag : hooks.retagPointer choice input destination.layout.ty before = .ok (some adjusted) afterRetag)
    (write : hooks.writeNoValidate choice adjusted.imm destination afterRetag = .ok () afterWrite)
    (encoded : Scalar.fromMaybePointer hooks.target.base place.mplace.ptr = .ok scalar)
    (nonnull : hooks.scalarMayBeNull choice scalar = pure false)
    (inhabited : hooks.opsemInhabited choice place.layout.ty = pure true)
    (aligned : hooks.checkPointerAlignResult choice place.mplace.ptr align afterWrite = .ok (.ok ()) afterWrite) :
    source_check_safe hooks choice (referenceSession name) destination destination.layout.ty (.reference true) before =
      .ok (referenceSession name) afterWrite := by
  unfold_typed ".ValidityVisitor.checkSafe"
  simp only [read, bind, EStateM.bind, pure, EStateM.pure, referenceSession]
  unfold_typed ".ValidityVisitor.markPlace"
  simp only [Option.isNone_none, Bool.true_eq, ↓reduceIte,
    bind, EStateM.bind, pure, EStateM.pure, construct]
  simp only [unsized, Bool.not_false, Bool.true_eq, ↓reduceIte, metadata, dynamic,
    bind, EStateM.bind, pure, EStateM.pure, Option.getD_some, checked]
  unfold ValidityVisitor.retagSafePointer ValidityVisitor.mapRetagOutcome
  simp only [retag, bind, EStateM.bind, pure, EStateM.pure, write]
  unfold_typed ".ValidityVisitor.liftResult"
  simp only [encoded, Except.mapError, nonnull, inhabited,
    bind, EStateM.bind, pure, EStateM.pure, Bool.false_eq_true, Bool.not_true, ↓reduceIte]
  unfold ValidityVisitor.mapPointerAlignmentOutcome
  simp only [aligned, bind, EStateM.bind, pure, EStateM.pure]

/-- The visitor's sampled validation policy does not trigger nested validation in ghost mode. -/
theorem visitor_write_local_ghost {K U C : Type} [DecidableEq K]
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (localId : Miri.MIR.LocalId)
    (old value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true) (debug : compiler.debugAssertions = false)
    (noDebug : compiler.debugAbiCheck value layout = pure ())
    (ghost : machine.user.payload.ghost = true) :
    (do
      let validate ← ValidityMachine.enforceValidity
      ValidityMemory.writeNoValidate (ValidityMachine.memoryEnvironment access)
        (ValidityMachine.placeHooks access allocation compiler) choice (fun _ => validate) value
        (LocalPlaces.localRuntimePlace frames.size frame localId layout))
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {frame with locals := (frame.locals.set localId
          {value := .live (.immediate value), layout := frame.locals[localId].layout} valid)} machine) := by
  simp only [ValidityMachine.enforceValidity, get, getThe, MonadStateOf.get, EStateM.get,
    bind, EStateM.bind, pure, EStateM.pure]
  exact write_local_ghost access allocation compiler choice frames frame machine localId old value layout
    valid live cached sized debug noDebug ghost _

#print axioms visitor_write_local_ghost

/-- Lift the real reference checker through the source primitive visitor. -/
theorem visit_reference_of_check {S C E F A Pad : Type}
    (hooks : ValidityVisitor.Hooks Provenance S C E F A Pad) (choice : C)
    (fuel : Nat) (name : String) (destination : RuntimePlace Provenance)
    (before after : S)
    (classified : hooks.classify choice destination.layout.ty = pure (.reference true))
    (checked : source_check_safe hooks choice (referenceSession name) destination
      destination.layout.ty (.reference true) before = .ok (referenceSession name) after) :
    ValidityVisitor.visit hooks choice (fuel + 1) (referenceSession name) destination before =
      .ok (referenceSession name) after := by
  unfold ValidityVisitor.visit
  simp only [classified, bind, EStateM.bind, pure, EStateM.pure]
  unfold_typed ".ValidityVisitor.primitive"
  simp only [checked, bind, EStateM.bind, pure, EStateM.pure]

#print axioms visit_reference_of_check

/-- Source shallow validation, retaining all body mutations while restoring ghost mode. -/
theorem validate_reference_shallow_of_visit {K U C F A : Type}
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C
      MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (choice : C) (fuel : Nat) (name : String) (destination : RuntimePlace Provenance)
    (before after : ValidityMachine.State K U) (immediate : Immediate Provenance)
    (ghostBefore : before.machine.user.payload.ghost = false)
    (ghostAfter : after.machine.user.payload.ghost = true)
    (named : hooks.typeName choice destination.layout.ty = pure name)
    (ghostField : hooks.withGhostValidation (A := ValidityVisitor.Session Provenance) =
      @ValidityMachine.withGhostValidation K U (ValidityVisitor.Session Provenance))
    (toOp : hooks.toOp choice destination
      {before with machine := {before.machine with user := {before.machine.user with
        payload := {before.machine.user.payload with ghost := true}}}} =
      .ok ⟨.immediate immediate, destination.layout⟩
        {before with machine := {before.machine with user := {before.machine.user with
          payload := {before.machine.user.payload with ghost := true}}}})
    (visited : ValidityVisitor.visit hooks choice (fuel + 1) (referenceSession name) destination
      {before with machine := {before.machine with user := {before.machine.user with
        payload := {before.machine.user.payload with ghost := true}}}} =
      .ok (referenceSession name) after) :
    ValidityVisitor.validatePlace hooks choice (fuel + 1) destination false true before =
      .ok () {after with machine := {after.machine with user := {after.machine.user with
        payload := {after.machine.user.payload with ghost := false}}}} := by
  unfold ValidityVisitor.validatePlace
  simp only [named, bind, EStateM.bind, pure, EStateM.pure, Bool.false_eq_true, ↓reduceIte]
  rw [ghostField]
  unfold ValidityMachine.withGhostValidation
  simp only [ghostBefore, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, EStateM.bind]
  erw [toOp]
  simp only [bind, EStateM.bind]
  erw [visited]
  simp only [bind, EStateM.bind]
  unfold_typed ".ValidityVisitor.resetPadding"
  simp only [referenceSession, bind, EStateM.bind, pure, EStateM.pure, ghostAfter, ↓reduceIte]

#print axioms validate_reference_shallow_of_visit

theorem check_reference_stage_for {S C E F A Pad : Type}
    (hooks : ValidityVisitor.Hooks Provenance S C E F A Pad) (choice : C)
    (name : String) (mutable : Bool) (destination : RuntimePlace Provenance) (input adjusted : RvalueImmTy Provenance)
    (place : MPlaceTy Provenance) (size : Size) (align : Align) (scalar : Scalar Provenance)
    (before afterRetag afterWrite : S)
    (read : hooks.readImmediate choice destination .reference before = .ok input before)
    (construct : hooks.ptrToPlace choice input = pure place)
    (unsized : place.layout.layout.isSized = false)
    (metadata : source_check_metadata hooks choice place = pure ())
    (dynamic : hooks.sizeAndAlign choice place before = .ok (some (size, align)) before)
    (checked : hooks.checkPointerAccess choice place.mplace.ptr size before = .ok (.ok ()) before)
    (retag : hooks.retagPointer choice input destination.layout.ty before = .ok (some adjusted) afterRetag)
    (write : hooks.writeNoValidate choice adjusted.imm destination afterRetag = .ok () afterWrite)
    (encoded : Scalar.fromMaybePointer hooks.target.base place.mplace.ptr = .ok scalar)
    (nonnull : hooks.scalarMayBeNull choice scalar = pure false)
    (inhabited : hooks.opsemInhabited choice place.layout.ty = pure true)
    (aligned : hooks.checkPointerAlignResult choice place.mplace.ptr align afterWrite = .ok (.ok ()) afterWrite) :
    source_check_safe hooks choice (referenceSession name) destination destination.layout.ty (.reference mutable) before =
      .ok (referenceSession name) afterWrite := by
  unfold_typed ".ValidityVisitor.checkSafe"
  simp only [read, bind, EStateM.bind, pure, EStateM.pure, referenceSession]
  unfold_typed ".ValidityVisitor.markPlace"
  simp only [Option.isNone_none, Bool.true_eq, ↓reduceIte,
    bind, EStateM.bind, pure, EStateM.pure, construct]
  simp only [unsized, Bool.not_false, Bool.true_eq, ↓reduceIte, metadata, dynamic,
    bind, EStateM.bind, pure, EStateM.pure, Option.getD_some, checked]
  unfold ValidityVisitor.retagSafePointer ValidityVisitor.mapRetagOutcome
  simp only [retag, bind, EStateM.bind, pure, EStateM.pure, write]
  unfold_typed ".ValidityVisitor.liftResult"
  simp only [encoded, Except.mapError, nonnull, inhabited,
    bind, EStateM.bind, pure, EStateM.pure, Bool.false_eq_true, Bool.not_true, ↓reduceIte]
  unfold ValidityVisitor.mapPointerAlignmentOutcome
  simp only [aligned, bind, EStateM.bind, pure, EStateM.pure]

theorem visit_reference_of_check_for {S C E F A Pad : Type}
    (hooks : ValidityVisitor.Hooks Provenance S C E F A Pad) (choice : C)
    (fuel : Nat) (name : String) (mutable : Bool) (destination : RuntimePlace Provenance)
    (before after : S)
    (classified : hooks.classify choice destination.layout.ty = pure (.reference mutable))
    (checked : source_check_safe hooks choice (referenceSession name) destination
      destination.layout.ty (.reference mutable) before = .ok (referenceSession name) after) :
    ValidityVisitor.visit hooks choice (fuel + 1) (referenceSession name) destination before =
      .ok (referenceSession name) after := by
  unfold ValidityVisitor.visit
  simp only [classified, bind, EStateM.bind, pure, EStateM.pure]
  unfold_typed ".ValidityVisitor.primitive"
  simp only [checked, bind, EStateM.bind, pure, EStateM.pure]

end DuplicatePrefix.ReferenceValidity

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ReferenceValidity.validity_read_pair,
      ``DuplicatePrefix.ReferenceValidity.read_local_pair_ghost,
      ``DuplicatePrefix.ReferenceValidity.write_local_ghost,
      ``DuplicatePrefix.ReferenceValidity.write_same_local_ghost,
      ``DuplicatePrefix.ReferenceValidity.metadata_slice,
      ``DuplicatePrefix.ReferenceValidity.visit_reference_of_check,
      ``DuplicatePrefix.ReferenceValidity.check_reference_stage,
      ``DuplicatePrefix.ReferenceValidity.check_reference_stage_at,
      ``DuplicatePrefix.ReferenceValidity.check_reference_stage_for,
      ``DuplicatePrefix.ReferenceValidity.visit_reference_of_check_for,
      ``DuplicatePrefix.ReferenceValidity.visitor_write_local_ghost,
      ``DuplicatePrefix.ReferenceValidity.validate_reference_shallow_of_visit] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
