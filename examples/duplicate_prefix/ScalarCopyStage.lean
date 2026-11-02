import duplicate_prefix.CopyIntrinsic
import duplicate_prefix.ScalarOperations
import duplicate_prefix.LocalPlaces
import duplicate_prefix.LocalWrites
import Miri.Interpreter.ValidityMachine
import Miri.Interpreter.TypedMachineBindings
import Miri.Input.CompilerCopy
import Miri.Input.CompilerCovariance
import Miri.Interpreter.TypedValidityProviders

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

namespace DuplicatePrefix.ScalarCopyStage
open Lean Elab in
elab "source_reset_padding" : term => do
  let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith (".ValidityVisitor.resetPadding" : String) then some name else none
  match found with
  | [name] => return mkConst name
  | _ => throwError "expected exact validity resetPadding"

open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open DuplicatePrefix.AllocationCopy

theorem same_type_copy (compiler : CompilerProviders.Prepared) (layout : LocalLayout) :
    CompilerCovariance.compatible compiler false layout layout = .ok true := by
  simp [CompilerCovariance.compatible, CompilerCovariance.relation, CompilerCovariance.relationWithIndex,
    bind, Except.bind, pure, Except.pure, Except.mapError]

theorem scalar_has_no_padding (runtime : RuntimeMetadata) (debug : Bool) (layout : LocalLayout)
    (scalar : Miri.ABI.Scalar) (repr : layout.layout.backendRepr = .Scalar scalar) :
    CompilerCopy.hasPadding runtime debug layout = .ok false := by
  simp [CompilerCopy.hasPadding, repr, pure, Except.pure]

theorem place_to_op_ghost [DecidableEq K]
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : Miri.MIR.LocalId) (layout : LocalLayout) (immediate : Immediate Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate immediate))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true)
    (debug : compiler.debugAssertions = false)
    (ghost : machine.user.payload.ghost = true) :
    placeToOp (ValidityMachine.placeHooks access allocation compiler) choice
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨.immediate immediate, layout⟩ (Storage.withCurrent framesBefore frame machine) := by
  unfold placeToOp placeToOpCore
  simp [ValidityMachine.placeHooks, ValidityMachine.compilerPolicy, PlaceMachine.placeHooks,
    LocalPlaces.localRuntimePlace, PlaceMachine.localToOp, PlaceMachine.localToOpCore,
    PlaceMachine.layoutLocal, MachineHooks.currentFrame, Storage.withCurrent,
    Stack.currentFrame?, Stack.frameIndex, Frame.getLocal, Frame.getLocalOperand, LocalState.access,
    valid, live, cached, sized, debug, ghost, ValidityMachine.validationInProgress,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, Except.pure, Except.bind, Except.mapError]

theorem validity_read_scalar [DecidableEq K]
    (access : ValidityMachine.Access K U) (state : ValidityMachine.State K U)
    (layout : LocalLayout) (value : Miri.Memory.Scalar Provenance)
    (primitive : Primitive) (range : WrappingRange)
    (repr : layout.layout.backendRepr = .Scalar (.Initialized (value := primitive) (validRange := range)))
    (retain : access.retainTouched = fun machine _ => machine)
    (expected : Miri.Memory.ExpectedValue) :
    ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access)
      ⟨.immediate (.scalar value), layout⟩ expected state = .ok ⟨.scalar value, layout⟩ state := by
  unfold ValidityMemory.readImmediate Miri.Interpreter.readImmediate
  unfold_internal ".Miri.Interpreter.isPrimitiveReadable"
  unfold_internal ".ValidityMemory.commit"
  simp [ValidityMachine.memoryEnvironment, localMemoryLayout, repr, Miri.Interpreter.readImmediateRaw,
    retain, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    pure, Pure.pure, EStateM.pure, Except.pure, Except.bind, Except.mapError, Id.run, Id.instMonad]

theorem clear_integer_local_ghost [DecidableEq K]
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : Miri.MIR.LocalId) (layout : LocalLayout) (bits : ScalarInt)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (.scalar (Scalar.fromScalarInt bits))))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true)
    (debug : compiler.debugAssertions = false)
    (ghost : machine.user.payload.ghost = true) :
    ValidityMemory.clearPlaceProvenance (ValidityMachine.memoryEnvironment access)
      (ValidityMachine.placeHooks access allocation compiler) choice ValidityMachine.validationInProgress
      MachineHooks.afterLocalWrite (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout)
      (Storage.withCurrent framesBefore frame machine) = .ok () (Storage.withCurrent framesBefore frame machine) := by
  unfold ValidityMemory.clearPlaceProvenance
  simp only [bind, EStateM.bind]
  rw [place_to_op_ghost access allocation compiler choice framesBefore frame machine localId layout
    (.scalar (Scalar.fromScalarInt bits)) valid live cached sized debug ghost]
  simp [Immediate.hasProvenance, Scalar.isPointer, Scalar.fromScalarInt, pure, EStateM.pure]

private theorem visit_primitive
    (hooks : ValidityVisitor.Hooks Provenance S C E F A Pad) (choice : C) (fuel : Nat)
    (session : ValidityVisitor.Session Provenance) (place : RuntimePlace Provenance)
    (state : S) (kind : ValidityVisitor.TypeKind) (value : Miri.Memory.Scalar Provenance)
    (supported : kind = .integer ∨ ∃ b, kind = .boolean ∧ value = Scalar.fromBool b)
    (classification : hooks.classify choice place.layout.ty state = .ok kind state)
    (read : hooks.readImmediate choice place .integer state = .ok ⟨.scalar value, place.layout⟩ state)
    (readBool : hooks.readImmediate choice place .boolean state = .ok ⟨.scalar value, place.layout⟩ state)
    (clear : hooks.clearProvenance choice place state = .ok () state)
    (reset : session.flags.resetProvenanceAndPadding = true)
    (noRanges : session.dataBytes = none) :
    ValidityVisitor.visit hooks choice (fuel + 1) session place state = .ok session state := by
  rcases supported with integer | ⟨b, boolean, valueEq⟩
  · subst kind
    unfold ValidityVisitor.visit
    unfold_internal ".ValidityVisitor.primitive"
    unfold_internal ".ValidityVisitor.scalarOf"
    unfold_internal ".ValidityVisitor.liftResult"
    unfold_internal ".ValidityVisitor.markPlace"
    simp [classification, read, clear, reset, noRanges, Immediate.toScalar,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, Except.mapError]
  · subst kind
    subst value
    unfold ValidityVisitor.visit
    unfold_internal ".ValidityVisitor.primitive"
    unfold_internal ".ValidityVisitor.scalarOf"
    unfold_internal ".ValidityVisitor.liftResult"
    unfold_internal ".ValidityVisitor.markPlace"
    simp [classification, readBool, clear, reset, noRanges, Immediate.toScalar,
      ScalarOperations.bool_scalar_roundtrip,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, Except.mapError]

theorem validate_primitive_local_shallow [DecidableEq K]
    (base : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (retagBudget fuel : Nat) (choice : C)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : Miri.MIR.LocalId) (layout : LocalLayout) (bits : ScalarInt)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (.scalar (Scalar.fromScalarInt bits))))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true)
    (primitive : Primitive) (range : WrappingRange)
    (repr : layout.layout.backendRepr = .Scalar (.Initialized (value := primitive) (validRange := range)))
    (debug : compiler.debugAssertions = false)
    (ghost : machine.user.payload.ghost = false)
    (retain : access.retainTouched = fun machine _ => machine)
    (name : String) (kind : ValidityVisitor.TypeKind)
    (nameQuery : base.typeName choice layout.ty = pure name)
    (kindQuery : base.classify choice layout.ty = pure kind)
    (supported : kind = .integer ∨ ∃ b, kind = .boolean ∧ Scalar.fromScalarInt (Prov := Provenance) bits = Scalar.fromBool b) :
    let hooks := TypedMachineBindings.bindValidity (ValidityMachine.visitor base access allocation compiler retag retagBudget) retag retagBudget
    ValidityVisitor.validatePlace hooks choice (fuel + 1)
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout) false true
      (Storage.withCurrent framesBefore frame machine) = .ok () (Storage.withCurrent framesBefore frame machine) := by
  dsimp only
  let hooks := TypedMachineBindings.bindValidity (ValidityMachine.visitor base access allocation compiler retag retagBudget) retag retagBudget
  let place := LocalPlaces.localRuntimePlace framesBefore.size frame localId layout
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent framesBefore frame activeMachine
  let initial : ValidityVisitor.Session Provenance := {
    path := ⟨name, #[]⟩, flags := ⟨true, false⟩, ctfeMode := none, refTracking := none, dataBytes := none }
  have toOp : hooks.toOp choice place active = .ok ⟨.immediate (.scalar (Scalar.fromScalarInt bits)), layout⟩ active := by
    exact place_to_op_ghost access allocation (ValidityMachine.compilerPolicy compiler) choice framesBefore frame
      activeMachine localId layout (.scalar (Scalar.fromScalarInt bits)) valid live cached sized debug rfl
  have read (expected : Miri.Memory.ExpectedValue) : hooks.readImmediate choice place expected active =
      .ok ⟨.scalar (Scalar.fromScalarInt bits), layout⟩ active := by
    change (do
      let op ← placeToOp (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy compiler)) choice place
      ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access) op expected) active = _
    simp only [bind, EStateM.bind]
    rw [place_to_op_ghost access allocation (ValidityMachine.compilerPolicy compiler) choice framesBefore frame
      activeMachine localId layout (.scalar (Scalar.fromScalarInt bits)) valid live cached sized debug rfl]
    simp only
    exact validity_read_scalar access active layout (Scalar.fromScalarInt bits) primitive range repr retain expected
  have clear : hooks.clearProvenance choice place active = .ok () active := by
    exact clear_integer_local_ghost access allocation (ValidityMachine.compilerPolicy compiler) choice framesBefore frame
      activeMachine localId layout bits valid live cached sized debug rfl
  have classified : hooks.classify choice place.layout.ty active = .ok kind active := by
    have kindAction : hooks.classify choice place.layout.ty = pure kind := kindQuery
    rw [kindAction]
    rfl
  have visit : ValidityVisitor.visit hooks choice (fuel + 1) initial place active = .ok initial active :=
    visit_primitive hooks choice fuel initial place active kind (Scalar.fromScalarInt bits) supported classified
      (read .integer) (read .boolean) clear rfl rfl
  have named : hooks.typeName choice place.layout.ty = pure name := nameQuery
  change ValidityVisitor.validatePlace hooks choice (fuel + 1) place false true _ = _
  unfold ValidityVisitor.validatePlace
  rw [named]
  simp only [bind, EStateM.bind, pure, EStateM.pure, Bool.false_eq_true, ↓reduceIte]
  have withGhost : hooks.withGhostValidation (A := ValidityVisitor.Session Provenance) =
      @ValidityMachine.withGhostValidation K U (ValidityVisitor.Session Provenance) := by rfl
  rw [withGhost]
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


theorem validate_primitive_fields_shallow [DecidableEq K]
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (fuel : Nat) (choice : C)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : Miri.MIR.LocalId) (layout : LocalLayout) (bits : ScalarInt)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (.scalar (Scalar.fromScalarInt bits))))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true)
    (primitive : Primitive) (range : WrappingRange)
    (repr : layout.layout.backendRepr = .Scalar (.Initialized (value := primitive) (validRange := range)))
    (debug : compiler.debugAssertions = false)
    (ghost : machine.user.payload.ghost = false)
    (retain : access.retainTouched = fun machine _ => machine)
    (name : String) (kind : ValidityVisitor.TypeKind)
    (nameQuery : hooks.typeName choice layout.ty = pure name)
    (kindQuery : hooks.classify choice layout.ty
      (Storage.withCurrent framesBefore frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}) =
      .ok kind (Storage.withCurrent framesBefore frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}))
    (supported : kind = .integer ∨ ∃ b, kind = .boolean ∧ Scalar.fromScalarInt (Prov := Provenance) bits = Scalar.fromBool b)
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
  have toOp : hooks.toOp choice place active = .ok ⟨.immediate (.scalar (Scalar.fromScalarInt bits)), layout⟩ active := by
    rw [toOpField]
    exact place_to_op_ghost access allocation (ValidityMachine.compilerPolicy compiler) choice framesBefore frame
      activeMachine localId layout (.scalar (Scalar.fromScalarInt bits)) valid live cached sized debug rfl
  have read (expected : Miri.Memory.ExpectedValue) : hooks.readImmediate choice place expected active =
      .ok ⟨.scalar (Scalar.fromScalarInt bits), layout⟩ active := by
    rw [readField]
    change (do
      let op ← placeToOp (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy compiler)) choice place
      ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access) op expected) active = _
    simp only [bind, EStateM.bind]
    rw [place_to_op_ghost access allocation (ValidityMachine.compilerPolicy compiler) choice framesBefore frame
      activeMachine localId layout (.scalar (Scalar.fromScalarInt bits)) valid live cached sized debug rfl]
    simp only
    exact validity_read_scalar access active layout (Scalar.fromScalarInt bits) primitive range repr retain expected
  have clear : hooks.clearProvenance choice place active = .ok () active := by
    rw [clearField]
    exact clear_integer_local_ghost access allocation (ValidityMachine.compilerPolicy compiler) choice framesBefore frame
      activeMachine localId layout bits valid live cached sized debug rfl
  have classified : hooks.classify choice place.layout.ty active = .ok kind active := kindQuery
  have visit : ValidityVisitor.visit hooks choice (fuel + 1) initial place active = .ok initial active :=
    visit_primitive hooks choice fuel initial place active kind (Scalar.fromScalarInt bits) supported classified
      (read .integer) (read .boolean) clear rfl rfl
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


theorem typed_visitor_primitive_fields [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (base : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat) :
    let hooks := TypedMachineBindings.bindValidity
      (TypedValidityProviders.visitor prepared runtime access allocation compiler pointers retag budget base) retag budget
    ∃ inner : ValidityMachine.Compiler K U C,
      inner.debugAssertions = compiler.debugAssertions ∧
      hooks.toOp = (fun c place => placeToOp
        (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy inner)) c place) ∧
      hooks.readImmediate = (fun c place expected => do
        let op ← placeToOp (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy inner)) c place
        ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access) op expected) ∧
      hooks.clearProvenance = (fun c place => ValidityMemory.clearPlaceProvenance
        (ValidityMachine.memoryEnvironment access) (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy inner))
        c ValidityMachine.validationInProgress MachineHooks.afterLocalWrite place) ∧
      hooks.withGhostValidation (A := ValidityVisitor.Session Provenance) =
        @ValidityMachine.withGhostValidation K U (ValidityVisitor.Session Provenance) ∧
      hooks.classify = (CompilerFactAdapters.validityHooks prepared base).classify ∧
      hooks.typeName = (CompilerFactAdapters.validityHooks prepared base).typeName := by
  refine ⟨PointerPlaceMachine.bindCompiler access allocation (CompilerExecutionProviders.pointerCompiler prepared)
    (PlaceDynamic.withVTable base.projection.dynamic base.vtable) base.vtable base.projection.dynamicFuel compiler,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem typed_visitor_primitive_fields_unbound [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (base : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat) :
    let hooks := TypedValidityProviders.visitor prepared runtime access allocation compiler pointers retag budget base
    ∃ inner : ValidityMachine.Compiler K U C,
      inner.debugAssertions = compiler.debugAssertions ∧
      hooks.toOp = (fun c place => placeToOp
        (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy inner)) c place) ∧
      hooks.readImmediate = (fun c place expected => do
        let op ← placeToOp (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy inner)) c place
        ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access) op expected) ∧
      hooks.clearProvenance = (fun c place => ValidityMemory.clearPlaceProvenance
        (ValidityMachine.memoryEnvironment access) (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy inner))
        c ValidityMachine.validationInProgress MachineHooks.afterLocalWrite place) ∧
      hooks.withGhostValidation (A := ValidityVisitor.Session Provenance) =
        @ValidityMachine.withGhostValidation K U (ValidityVisitor.Session Provenance) ∧
      hooks.classify = (CompilerFactAdapters.validityHooks prepared base).classify ∧
      hooks.typeName = (CompilerFactAdapters.validityHooks prepared base).typeName := by
  refine ⟨PointerPlaceMachine.bindCompiler access allocation (CompilerExecutionProviders.pointerCompiler prepared)
    (PlaceDynamic.withVTable base.projection.dynamic base.vtable) base.vtable base.projection.dynamicFuel compiler,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem typed_visitor_wide_pointer_fields [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (base : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (retag : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat) :
    let hooks := TypedValidityProviders.visitor prepared runtime access allocation compiler pointers retag budget base
    ∃ inner : ValidityMachine.Compiler K U C,
      inner.debugAssertions = compiler.debugAssertions ∧
      inner.debugAbiCheck = compiler.debugAbiCheck ∧
      hooks.toOp = (fun c place => placeToOp
        (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy inner)) c place) ∧
      hooks.readImmediate = (fun c place expected => do
        let op ← placeToOp (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy inner)) c place
        ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment access) op expected) ∧
      hooks.writeNoValidate = (fun c value destination => do
        let validate ← ValidityMachine.enforceValidity
        ValidityMemory.writeNoValidate (ValidityMachine.memoryEnvironment access)
          (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy inner))
          c (fun _ => validate) value destination) ∧
      hooks.ptrToPlace = PointerPlaceMachine.fromImmediate access
        (CompilerExecutionProviders.pointerCompiler prepared) ∧
      hooks.metadataTail = (CompilerFactAdapters.validityHooks prepared base).metadataTail ∧
      hooks.target = base.target ∧
      hooks.withGhostValidation (A := ValidityVisitor.Session Provenance) =
        @ValidityMachine.withGhostValidation K U (ValidityVisitor.Session Provenance) ∧
      hooks.classify = (CompilerFactAdapters.validityHooks prepared base).classify ∧
      hooks.typeName = (CompilerFactAdapters.validityHooks prepared base).typeName := by
  refine ⟨PointerPlaceMachine.bindCompiler access allocation (CompilerExecutionProviders.pointerCompiler prepared)
    (PlaceDynamic.withVTable base.projection.dynamic base.vtable) base.vtable base.projection.dynamicFuel compiler,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem read_raw_immediate [DecidableEq K]
    (access : PlaceMachine.AccessConfig K U) (state : MachineHooks.State K U)
    (layout : LocalLayout) (value : Immediate Provenance)
    (retain : access.retainTouched = fun machine _ => machine) :
    PlaceMachine.readRaw access ⟨.immediate value, layout⟩ state =
      .ok (.immediate ⟨value, localMemoryLayout layout⟩) state := by
  unfold PlaceMachine.readRaw Miri.Interpreter.readImmediateRaw
  unfold_internal ".PlaceMachine.commit"
  unfold_internal ".PlaceMachine.finish"
  simp [retain, get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    pure, Pure.pure, EStateM.pure, Except.pure, Except.bind, Except.mapError, Id.run, Id.instMonad]

theorem copy_immediate_no_validate [DecidableEq K]
    (place : PlaceHooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra)
    (copy : PlaceCopyHooks Provenance (MachineHooks.State K U) C)
    (access : PlaceMachine.AccessConfig K U) (compiler : CompilerProviders.Prepared)
    (choice : C) (state : MachineHooks.State K U)
    (layout : LocalLayout) (value : Immediate Provenance) (dest : RuntimePlace Provenance)
    (destLayout : dest.layout = layout)
    (scalar : Miri.ABI.Scalar) (repr : layout.layout.backendRepr = .Scalar scalar)
    (sized : layout.layout.isSized = true)
    (compatibleField : copy.compatible = CompilerCovariance.compatible compiler false)
    (paddingField : copy.hasPadding = CompilerCopy.hasPadding compiler.runtime false)
    (rawField : copy.readRaw = fun _ => PlaceMachine.readRaw access)
    (retain : access.retainTouched = fun machine _ => machine) :
    copyRuntimePlaceNoValidate place copy choice ⟨.immediate value, layout⟩ dest false state =
      writePlaceImmediateNoValidate place choice value dest state := by
  unfold copyRuntimePlaceNoValidate
  unfold_internal ".Interpreter.placeLift"
  simp only [destLayout, compatibleField, same_type_copy, paddingField,
    scalar_has_no_padding compiler.runtime false layout scalar repr,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [rawField]
  simp [bind, Bind.bind, EStateM.bind, EStateM.pure]
  rw [read_raw_immediate access state layout value retain]
  simp [sized, localMemoryLayout, bind, EStateM.bind, pure, EStateM.pure]

/-- Same-layout initialized scalar copying executes exactly the real immediate
writer, including its actual validity check and validation callback. -/
theorem copy_immediate [DecidableEq K]
    (place : PlaceHooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra)
    (copy : PlaceCopyHooks Provenance (MachineHooks.State K U) C)
    (access : PlaceMachine.AccessConfig K U) (compiler : CompilerProviders.Prepared)
    (choice : C) (layout : LocalLayout) (value : Immediate Provenance) (dest : RuntimePlace Provenance)
    (destLayout : dest.layout = layout)
    (scalar : Miri.ABI.Scalar) (repr : layout.layout.backendRepr = .Scalar scalar)
    (sized : layout.layout.isSized = true)
    (compatibleField : copy.compatible = CompilerCovariance.compatible compiler false)
    (paddingField : copy.hasPadding = CompilerCopy.hasPadding compiler.runtime false)
    (rawField : copy.readRaw = fun _ => PlaceMachine.readRaw access)
    (retain : access.retainTouched = fun machine _ => machine) :
    copyRuntimePlace place copy choice ⟨.immediate value, layout⟩ dest false =
      writePlaceImmediate place choice value dest := by
  have core : copyRuntimePlaceNoValidate place copy choice ⟨.immediate value, layout⟩ dest false =
      writePlaceImmediateNoValidate place choice value dest := by
    funext state
    exact copy_immediate_no_validate place copy access compiler choice state layout value dest
      destLayout scalar repr sized compatibleField paddingField rawField retain
  unfold copyRuntimePlace writePlaceImmediate
  rw [core]
  simp only [destLayout, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]

theorem rvalue_copy_immediate [DecidableEq K]
    (execution : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (compiler : CompilerProviders.Prepared) (choice : C)
    (layout : LocalLayout) (value : Immediate Provenance) (dest : RuntimePlace Provenance)
    (destLayout : dest.layout = layout)
    (scalar : Miri.ABI.Scalar) (repr : layout.layout.backendRepr = .Scalar scalar)
    (sized : layout.layout.isSized = true)
    (compatibleField : (ExecutionMachine.withValidation execution limits).copy.compatible = CompilerCovariance.compatible compiler false)
    (paddingField : (ExecutionMachine.withValidation execution limits).copy.hasPadding = CompilerCopy.hasPadding compiler.runtime false)
    (retain : execution.access.retainTouched = fun machine _ => machine) :
    (ExecutionMachine.rvalueHooks execution limits).copyOp choice ⟨.immediate value, layout⟩ dest =
      (ExecutionMachine.rvalueHooks execution limits).writeImmediate choice value dest := by
  exact copy_immediate (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation execution limits)).place
    (ExecutionMachine.withValidation execution limits).copy execution.access compiler choice layout value dest
    destLayout scalar repr sized compatibleField paddingField (by rfl) retain

theorem copy_no_padding_no_validate [DecidableEq K]
    (place : PlaceHooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra)
    (copy : PlaceCopyHooks Provenance (MachineHooks.State K U) C)
    (access : PlaceMachine.AccessConfig K U) (compiler : CompilerProviders.Prepared)
    (choice : C) (state : MachineHooks.State K U)
    (layout : LocalLayout) (value : Immediate Provenance) (dest : RuntimePlace Provenance)
    (destLayout : dest.layout = layout)
    (padding : CompilerCopy.hasPadding compiler.runtime false layout = .ok false)
    (sized : layout.layout.isSized = true)
    (compatibleField : copy.compatible = CompilerCovariance.compatible compiler false)
    (paddingField : copy.hasPadding = CompilerCopy.hasPadding compiler.runtime false)
    (rawField : copy.readRaw = fun _ => PlaceMachine.readRaw access)
    (retain : access.retainTouched = fun machine _ => machine) :
    copyRuntimePlaceNoValidate place copy choice ⟨.immediate value, layout⟩ dest false state =
      writePlaceImmediateNoValidate place choice value dest state := by
  unfold copyRuntimePlaceNoValidate
  unfold_internal ".Interpreter.placeLift"
  simp only [destLayout, compatibleField, same_type_copy, paddingField,
    padding,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [rawField]
  simp [bind, Bind.bind, EStateM.bind, EStateM.pure]
  rw [read_raw_immediate access state layout value retain]
  simp [sized, localMemoryLayout, bind, EStateM.bind, pure, EStateM.pure]

/-- Same-layout initialized scalar copying executes exactly the real immediate
writer, including its actual validity check and validation callback. -/
theorem copy_no_padding [DecidableEq K]
    (place : PlaceHooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra)
    (copy : PlaceCopyHooks Provenance (MachineHooks.State K U) C)
    (access : PlaceMachine.AccessConfig K U) (compiler : CompilerProviders.Prepared)
    (choice : C) (layout : LocalLayout) (value : Immediate Provenance) (dest : RuntimePlace Provenance)
    (destLayout : dest.layout = layout)
    (padding : CompilerCopy.hasPadding compiler.runtime false layout = .ok false)
    (sized : layout.layout.isSized = true)
    (compatibleField : copy.compatible = CompilerCovariance.compatible compiler false)
    (paddingField : copy.hasPadding = CompilerCopy.hasPadding compiler.runtime false)
    (rawField : copy.readRaw = fun _ => PlaceMachine.readRaw access)
    (retain : access.retainTouched = fun machine _ => machine) :
    copyRuntimePlace place copy choice ⟨.immediate value, layout⟩ dest false =
      writePlaceImmediate place choice value dest := by
  have core : copyRuntimePlaceNoValidate place copy choice ⟨.immediate value, layout⟩ dest false =
      writePlaceImmediateNoValidate place choice value dest := by
    funext state
    exact copy_no_padding_no_validate place copy access compiler choice state layout value dest
      destLayout padding sized compatibleField paddingField rawField retain
  unfold copyRuntimePlace writePlaceImmediate
  rw [core]
  simp only [destLayout, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]

theorem rvalue_copy_no_padding [DecidableEq K]
    (execution : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    (compiler : CompilerProviders.Prepared) (choice : C)
    (layout : LocalLayout) (value : Immediate Provenance) (dest : RuntimePlace Provenance)
    (destLayout : dest.layout = layout)
    (padding : CompilerCopy.hasPadding compiler.runtime false layout = .ok false)
    (sized : layout.layout.isSized = true)
    (compatibleField : (ExecutionMachine.withValidation execution limits).copy.compatible = CompilerCovariance.compatible compiler false)
    (paddingField : (ExecutionMachine.withValidation execution limits).copy.hasPadding = CompilerCopy.hasPadding compiler.runtime false)
    (retain : execution.access.retainTouched = fun machine _ => machine) :
    (ExecutionMachine.rvalueHooks execution limits).copyOp choice ⟨.immediate value, layout⟩ dest =
      (ExecutionMachine.rvalueHooks execution limits).writeImmediate choice value dest := by
  exact copy_no_padding (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation execution limits)).place
    (ExecutionMachine.withValidation execution limits).copy execution.access compiler choice layout value dest
    destLayout padding sized compatibleField paddingField (by rfl) retain

theorem with_retag_mode_existing (mode : RetagPolicy.RetagMode)
    (action : MachineHooks.M K U A) (state after : MachineHooks.State K U)
    (tracker : MachineHooks.BorrowState) (value : A)
    (tracked : state.machine.borrowTracker = some tracker)
    (modeSame : tracker.retagMode = mode)
    (afterTracked : after.machine.borrowTracker = some tracker)
    (body : action state = .ok value after) :
    MachineHooks.withRetagMode mode action state = .ok value after := by
  have sameTracker : {tracker with retagMode := mode} = tracker := by rw [← modeSame]
  have entered : {state with machine := {state.machine with borrowTracker := some {tracker with retagMode := mode}}} = state := by
    rw [sameTracker, ← tracked]
  unfold MachineHooks.withRetagMode
  rw [tracked]
  dsimp only
  rw [entered, body]
  simp only [afterTracked]
  change EStateM.Result.ok value {after with machine := {after.machine with borrowTracker := some tracker}} = EStateM.Result.ok value after
  rw [← afterTracked]
#print axioms with_retag_mode_existing
#print axioms rvalue_copy_immediate

#print axioms copy_immediate

#print axioms copy_immediate_no_validate
#print axioms read_raw_immediate

#print axioms typed_visitor_primitive_fields

#print axioms validate_primitive_fields_shallow
#print axioms validate_primitive_local_shallow
#print axioms visit_primitive

#print axioms validity_read_scalar
#print axioms clear_integer_local_ghost

#print axioms same_type_copy
#print axioms scalar_has_no_padding
#print axioms place_to_op_ghost
open Lean Elab Command in
run_cmd do
  for declaration in [``typed_visitor_wide_pointer_fields, ``copy_no_padding_no_validate, ``copy_no_padding, ``rvalue_copy_no_padding, ``with_retag_mode_existing, ``rvalue_copy_immediate, ``copy_immediate, ``copy_immediate_no_validate, ``read_raw_immediate, ``same_type_copy, ``scalar_has_no_padding, ``place_to_op_ghost,
      ``validity_read_scalar, ``clear_integer_local_ghost, ``visit_primitive,
      ``validate_primitive_local_shallow, ``validate_primitive_fields_shallow, ``typed_visitor_primitive_fields, ``typed_visitor_primitive_fields_unbound] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.ScalarCopyStage
