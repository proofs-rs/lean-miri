import empty_function.LocalUnit
import Miri.Interpreter.ExecutionMachine

/-! The actual unit-local assignment components and statement driver. Caller
frames and physical machine state are parameters; these lemmas do not execute
the caller's continuation. -/
namespace EmptyFunction.BodyStep
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
variable {K U C : Type} [DecidableEq K]
abbrev F := LocalUnit.F
abbrev current := @LocalUnit.current
abbrev withUnit := LocalUnit.withUnit

def destination (frames : Array F) (frame : F) (unit : LocalLayout) : RuntimePlace Provenance :=
  ⟨.local frames.size 0 none frame.localsIdentity,unit⟩

theorem evalPlace_current {O X Host : Type}
    (config : ExecutionMachine.Config K U C O X Host) (choice : C)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K U)
    (id : PlaceId) (skip : Bool) :
    ExecutionMachine.evalPlace config choice id skip (current frames frame machine) =
      PlaceTable.eval frame.mirTables (ExecutionMachine.projectionHooks config)
        (fun c id value => (ExecutionMachine.operandHooks config).checkPlaceType c id value.layout)
        choice id skip (current frames frame machine) := by
  simp [ExecutionMachine.evalPlace, MachineHooks.currentFrame, current, LocalUnit.current,
    Stack.currentFrame?, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

theorem evalOperandAt_current (hooks : OperandMachine.Hooks K U C) (choice : C)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K U)
    (path : OperandPath) (id : OperandId) (known : Option LocalLayout) :
    OperandTable.evalOperandAt hooks choice path id known (current frames frame machine) =
      OperandTable.eval frame.mirTables hooks (fun c id value => hooks.checkPlaceType c id value.layout)
        choice id known (some path) (current frames frame machine) := by
  simp [OperandTable.evalOperandAt, MachineHooks.currentFrame, current, LocalUnit.current,
    Stack.currentFrame?, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

/-- The destination lookup caches only the computed unit layout. -/
theorem layout_zero (compiler : PlaceMachine.CompilerHooks K U C) (choice : C)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K U)
    (unit : LocalLayout)
    (computed : compiler.layout choice 0 (current frames (withUnit frame .uninit none) machine) =
      .ok unit (current frames (withUnit frame .uninit none) machine)) :
    PlaceMachine.layoutLocal compiler choice 0 (current frames (withUnit frame .uninit none) machine) =
      .ok unit (current frames (withUnit frame .uninit (some unit)) machine) := by
  with_unfolding_all
   unfold PlaceMachine.layoutLocal
   simp [current, LocalUnit.current, withUnit, LocalUnit.withUnit, MachineHooks.currentFrame, Stack.currentFrame?, Frame.getLocal,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, Except.pure, EStateM.pure] at computed ⊢
   rw [computed]
   simp [Frame.getOrCacheLocalLayout, Frame.getLocal, MachineHooks.setCurrentFrame,
    current, LocalUnit.current, withUnit, LocalUnit.withUnit, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, set, MonadStateOf.set, EStateM.set,
    Except.pure, Except.bind]

/-- The optimized-local writer retains every machine component and caller frame.
The local already contains the unit representation, so its value is unchanged. -/
theorem write_zero (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K U)
    (unit : LocalLayout) (sized : unit.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none)
    (validation : MachineHooks.M K U Bool)
    (validationPure : ∀ state, ∃ flag, validation state = .ok flag state) :
    placeWriteLocalImmediate MachineHooks.currentFrame MachineHooks.setCurrentFrame
      validation MachineHooks.afterLocalWrite (fun _ _ => pure ()) 0 unit .uninit
      (current frames (withUnit frame .uninit (some unit)) machine) =
      .ok () (current frames (withUnit frame .uninit (some unit)) machine) := by
  obtain ⟨flag, flagEq⟩ := validationPure (current frames (withUnit frame .uninit (some unit)) machine)
  with_unfolding_all
   unfold placeWriteLocalImmediate
   simp [sized, MachineHooks.currentFrame, current, LocalUnit.current, withUnit, LocalUnit.withUnit, Stack.currentFrame?,
    stackLift_ok, LocalUnit.unit_operand, LocalUnit.replace_unit, Frame.getLocalOperand, Frame.getLocal, LocalState.access,
    Except.mapError, Except.pure, Frame.setLocalOperand, Frame.replaceLocalValue, Except.bind,
    MachineHooks.setCurrentFrame, get, getThe, MonadStateOf.get, EStateM.get,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, set, MonadStateOf.set, EStateM.set]
   change ((do
      unless ← validation do MachineHooks.afterLocalWrite 0 false
      pure ()) : MachineHooks.M K U Unit)
      (current frames (withUnit frame .uninit (some unit)) machine) = _
   simp only [bind, Bind.bind, EStateM.bind, flagEq, pure, Pure.pure, EStateM.pure]
   cases flag <;> simp [LocalUnit.write_no_clocks, withUnit, noClocks,
    MachineHooks.afterLocalWrite, MachineHooks.currentFrame, current, LocalUnit.current, LocalUnit.withUnit, Stack.currentFrame?,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

/-- The actual empty-projection destination evaluation computes and caches the
unit layout, and performs the configured debug-disabled type check. -/
theorem evaluate_zero (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (choice : C) (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (unit : LocalLayout) (sized : unit.layout.isSized = true)
    (source : projection.place = ValidityMachine.placeHooks access allocation compiler)
    (check : compiler.checkPlaceType = fun _ _ _ => pure ())
    (computed : compiler.layout choice 0 (current frames (withUnit frame .uninit none) machine) =
      .ok unit (current frames (withUnit frame .uninit none) machine)) :
    PlaceDynamic.evalPlace projection choice ⟨0,#[]⟩ true
      (current frames (withUnit frame .uninit none) machine) =
      .ok (destination frames frame unit)
        (current frames (withUnit frame .uninit (some unit)) machine) := by
  have layout := layout_zero compiler choice frames frame machine unit computed
  have localResult : localToPlace (ValidityMachine.placeHooks access allocation compiler) choice 0
      (current frames (withUnit frame .uninit none) machine) =
      .ok (destination frames frame unit)
        (current frames (withUnit frame .uninit (some unit)) machine) := by
    have placeLayout : placeLayoutOfLocal (ValidityMachine.placeHooks access allocation compiler)
        choice 0 (current frames (withUnit frame .uninit none) machine) =
        .ok unit (current frames (withUnit frame .uninit (some unit)) machine) := by
      simp only [current, LocalUnit.current, withUnit, LocalUnit.withUnit] at computed
      simp [placeLayoutOfLocal, ValidityMachine.placeHooks, ValidityMachine.compilerPolicy,
        PlaceMachine.placeHooks, MachineHooks.currentFrame, MachineHooks.setCurrentFrame,
        current, LocalUnit.current, withUnit, LocalUnit.withUnit, Stack.currentFrame?,
        Frame.getLocal, Frame.getOrCacheLocalLayout, computed,
        get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set,
        bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, Except.pure, Except.bind]
    unfold localToPlace
    simp only [bind, Bind.bind, EStateM.bind, placeLayout]
    simp [bind, Bind.bind, EStateM.bind, layout, sized, ValidityMachine.placeHooks,
      PlaceMachine.placeHooks, ValidityMachine.compilerPolicy, current, LocalUnit.current,
      MachineHooks.currentFrame, Stack.currentFrame?, Stack.frameIndex, destination, withUnit, LocalUnit.withUnit,
      get, getThe, MonadStateOf.get, EStateM.get, pure, Pure.pure, EStateM.pure,
      Except.pure]
  unfold PlaceDynamic.evalPlace
  simp only [source, bind, Bind.bind, EStateM.bind, localResult]
  simp [ValidityMachine.placeHooks, PlaceMachine.placeHooks, ValidityMachine.compilerPolicy,
    check, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]

/-- Reading the freshly cached unit local is state preserving, including the
actual ghost-mode read suppression and the no-clock ordinary read hook. -/
theorem read_place_zero (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (unit : LocalLayout) (sized : unit.layout.isSized = true)
    (debugOff : compiler.debugAssertions = false)
    (noClocks : frame.extra.dataRace = none) :
    placeToOp (ValidityMachine.placeHooks access allocation compiler) choice
      (destination frames frame unit)
      (current frames (withUnit frame .uninit (some unit)) machine) =
      .ok ⟨.immediate .uninit,unit⟩ (current frames (withUnit frame .uninit (some unit)) machine) := by
  cases flag : machine.user.payload.ghost <;> with_unfolding_all
    simp [placeToOp, placeToOpCore, ValidityMachine.placeHooks, ValidityMachine.compilerPolicy,
      PlaceMachine.placeHooks, PlaceMachine.localToOp, PlaceMachine.localToOpCore, PlaceMachine.layoutLocal,
      ValidityMachine.validationInProgress, destination, sized, debugOff, noClocks, flag,
      MachineHooks.afterLocalRead, MachineHooks.currentFrame, current, LocalUnit.current,
      withUnit, LocalUnit.withUnit, Frame.getLocalOperand, Frame.getLocal, Stack.frameIndex,
      Stack.currentFrame?, LocalState.access, Except.mapError, Except.pure, Except.bind,
      get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]

/-- The actual scoped place writer uses the immediate-local path for the
sole unit local. No physical memory operation is invoked. -/
theorem write_place_zero (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (unit : LocalLayout) (sized : unit.layout.isSized = true)
    (debugOff : compiler.debugAssertions = false)
    (abiOff : compiler.debugAbiCheck = fun _ _ => pure ())
    (noClocks : frame.extra.dataRace = none) :
    writePlaceImmediateNoValidate (ValidityMachine.placeHooks access allocation compiler) choice .uninit
      (destination frames frame unit)
      (current frames (withUnit frame .uninit (some unit)) machine) =
      .ok () (current frames (withUnit frame .uninit (some unit)) machine) := by
  have write := write_zero frames frame machine unit sized noClocks
    ValidityMachine.validationInProgress (fun state => ⟨_, rfl⟩)
  with_unfolding_all
    unfold writePlaceImmediateNoValidate asMplaceOrMutableLocal
    simp [ValidityMachine.placeHooks, ValidityMachine.compilerPolicy, PlaceMachine.placeHooks,
      requireCurrent_eq, checkLocalIdentity_debugOff, destination, sized, debugOff, abiOff, current, LocalUnit.current,
      MachineHooks.currentFrame, Stack.currentFrame?, Stack.frameIndex,
      get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure, withUnit, LocalUnit.withUnit,
      Frame.getLocalOperand, Frame.getLocal, LocalState.access, Except.mapError, Except.pure, Except.bind]
    change placeWriteLocalImmediate _ _ _ _ _ 0 unit .uninit _ = _
    exact write

/-- Source copy performs a unit immediate-local write even when the layout's
Memory ABI reports padding. Its pure layout checks do not touch the heap. -/
theorem copy_zero_no_validate (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (copy : PlaceCopyHooks Provenance (ValidityMachine.State K U) C) (choice : C)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (unit : LocalLayout) (sized : unit.layout.isSized = true)
    (debugOff : compiler.debugAssertions = false)
    (abiOff : compiler.debugAbiCheck = fun _ _ => pure ())
    (compatible : copy.compatible unit unit = .ok true)
    (padding : copy.hasPadding unit = .ok true)
    (noClocks : frame.extra.dataRace = none) :
    copyRuntimePlaceNoValidate (ValidityMachine.placeHooks access allocation compiler) copy choice
      ⟨.immediate .uninit,unit⟩ (destination frames frame unit) false
      (current frames (withUnit frame .uninit (some unit)) machine) =
      .ok () (current frames (withUnit frame .uninit (some unit)) machine) := by
  simp only [copyRuntimePlaceNoValidate, destination, compatible, placeLift_ok,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure, Bool.not_true,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte, padding, Bool.not_false,
    sized, Bool.false_or, bne_self_eq_false]
  exact write_place_zero access allocation compiler choice frames frame machine unit sized
    debugOff abiOff noClocks

theorem step_missing_block (hooks : StepHooks Provenance LocalLayout MachineHooks.FrameExtra
      (MachineHooks.MachineState K U) C (RuntimePlace Provenance)) (choice : C)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K U)
    (location : MIR.Location) (id : MIR.BlockNodeId)
    (atLocation : frame.location = .mir location)
    (selected : frame.body.basicBlocks[location.block]? = some id)
    (absent : frame.mirTables.blocks.lookup id.index = .error id.index) :
    Step.step hooks choice (current frames frame machine) =
      (current frames frame machine, .error (.invalidProgram s!"invalid MIR block ID {id.index}")) := by
  simp [Step.step, current, LocalUnit.current, Stack.currentFrame?, atLocation, selected, absent]

/-- The real statement driver advances the freshly installed frame after its
assignment, without scheduling or executing a caller instruction. The assignment
premise is an internal composition edge, not an initial-input condition. -/
theorem assignment_driver (hooks : StepHooks Provenance LocalLayout MachineHooks.FrameExtra
      (MachineHooks.MachineState K U) C (RuntimePlace Provenance)) (choice : C)
    (frames : Array F) (before after : F) (machine : MachineHooks.MachineState K U)
    (blockId : MIR.BlockNodeId) (statementId : MIR.StatementId)
    (block : MIR.BlockNode) (statement : MIR.StatementNode) (place : MIR.PlaceId) (value : MIR.RvalueId)
    (beforeLoc : before.location = .mir ⟨0,0⟩)
    (afterLoc : after.location = .mir ⟨0,0⟩)
    (found : before.body.basicBlocks[0]? = some blockId)
    (blockFound : before.mirTables.blocks.lookup blockId.index = .ok block)
    (first : block.statements[0]? = some statementId)
    (statementFound : before.mirTables.statements.lookup statementId.index = .ok statement)
    (kind : statement.kind = .Assign place value)
    (assign : hooks.assign choice place value (current frames before machine) =
      (current frames after machine,.ok ())) :
    Step.step hooks choice (current frames before machine) =
      (current frames {after with location := .mir ⟨0,1⟩} machine,.ok true) := by
  have evaluated : Step.evalStatement hooks choice statement (current frames before machine) =
      (current frames after machine,.ok ()) := by
    simpa only [Step.evalStatement,kind] using assign
  unfold Step.step
  simp only [Stack.currentFrame?, current, LocalUnit.current, Array.back?_push,
    beforeLoc, found, blockFound, first, statementFound]
  simp only [current, LocalUnit.current] at evaluated
  erw [evaluated]
  simp [current, LocalUnit.current, Stack.currentFrame?, afterLoc, Array.set_push]

end EmptyFunction.BodyStep
