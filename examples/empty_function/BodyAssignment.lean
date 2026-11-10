import empty_function.BodyCopy
import empty_function.Literal

/-! The fixed empty_function statement evaluated with the canonical MIR rvalue and step
drivers. The sole local is freshly installed; callers and memory are arbitrary. -/
namespace EmptyFunction.BodyAssignment
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

private def literalType : StatementKind → Option TyId
  | .Assign _ (.Use (.Constant literal) _) => match literal.value with
    | .Val .ZeroSized ty => some ty
    | _ => none
  | _ => none

 theorem raw_unit_local (s : Static) (metadata : Metadata s) :
    s.loaded.body.locals = #[s.abi.ret.layout.ty] := by
  have mapped := congrArg (Option.map literalType) metadata.literalStatement
  rw [metadata.body] at mapped
  have source : ((((Program.root.loaded.body.basicBlocks[0]?).bind
      (fun block => block.statements[0]?)).map (fun stmt => stmt.kind)).map literalType) =
      some (some 0) := by rfl
  rw [source] at mapped
  simp only [Option.map_some, literalType, metadata.literalShape, Option.some.injEq] at mapped
  have raw : s.loaded.body.locals = #[0] := by rw [metadata.body]; rfl
  simpa only [mapped] using raw

 theorem constant (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (bodyIdentity : frame.bodyIdentity = s.loaded.identity)
    (function : frame.functionInstance = s.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩) :
    s.cfg.operands.constant ()
      metadata.literal (some s.abi.ret.layout)
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) =
      .ok ⟨.immediate .uninit,s.abi.ret.layout⟩
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig, capacity, Nat.add_assoc] using s.built
  have source := BodyConstantDictionary.fields_of_make s.prepared.compiler s.prepared.image s.bytes
    s.options leaves (remaining+1) metadata.construction s.cfg outer
  obtain ⟨functions, arithmetic, external, callback⟩ := source.constants
  have literal := Literal.eval_unit s.prepared.compiler.runtime functions arithmetic external
    MemoryErrors.constant metadata.literal s.abi.ret.layout
    (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) frames machine
    metadata.literalShape
  rw [callback profile.debug]
  simp only [MachineHooks.currentFrame,
    BodyStep.current, LocalUnit.current, Stack.currentFrame?, Array.back?_push,
    BodyStep.withUnit, LocalUnit.withUnit, location, bodyIdentity,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure]
  simpa [BodyStep.current, LocalUnit.current, BodyStep.withUnit, LocalUnit.withUnit,
    Array.map_push, bodyIdentity, location] using literal

private theorem bound_copy_eq (s : Static) (layout : LocalLayout)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (compatible : s.cfg.copy.compatible layout layout = .ok true)
    (padding : s.cfg.copy.hasPadding layout = .ok true)
    (sized : layout.layout.isSized = true) :
    (ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation s.cfg s.limits) s.limits).copyOp ()
      ⟨.immediate .uninit,layout⟩ (BodyStep.destination frames frame layout) =
    copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,layout⟩
      (BodyStep.destination frames frame layout) false := by
  funext state
  simp [ExecutionMachine.rvalueHooks, ExecutionMachine.withValidation,
    ExecutionMachine.projectionHooks, TypedMachineBindings.bindValidation,
    copyRuntimePlace, copyRuntimePlaceNoValidate, BodyStep.destination,
    compatible, padding, sized, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]


 theorem scoped_copy (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (positive : 0 < s.options.limits.validation)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    MachineHooks.withRetagMode .Default
      (copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,s.abi.ret.layout⟩
        (BodyStep.destination frames frame s.abi.ret.layout) false)
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) =
      .ok () (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
  cases trackerEq : machine.borrowTracker with
  | none =>
    simpa only [MachineHooks.withRetagMode, BodyStep.current, LocalUnit.current, trackerEq] using
      BodyCopy.unit s metadata profile remaining capacity positive frames frame machine noClocks noGhost shallow
  | some tracker =>
    let entered := {machine with borrowTracker := some {tracker with retagMode := .Default}}
    have copied := BodyCopy.unit s metadata profile remaining capacity positive frames frame entered
      noClocks noGhost shallow
    simp only [BodyStep.current, LocalUnit.current, entered] at copied
    unfold MachineHooks.withRetagMode
    simp only [BodyStep.current, LocalUnit.current, trackerEq]
    rw [copied]
    simp only []
    have restored : {machine with borrowTracker := some tracker} = machine := by
      rw [←trackerEq]
    simpa only [restored]

 theorem rvalue (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (positive : 0 < s.options.limits.validation)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (bodyIdentity : frame.bodyIdentity = s.loaded.identity)
    (body : frame.body = s.loaded.body)
    (function : frame.functionInstance = s.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation s.cfg s.limits) s.limits)
      () (.Use (.Constant metadata.literal) .Yes) ⟨0,#[]⟩
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      .ok () (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig, capacity, Nat.add_assoc] using s.built
  have source := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes
    s.options leaves (remaining+1) metadata.construction s.cfg outer
  have dictionaries := CanonicalDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes
    s.options leaves (remaining+1) metadata.construction s.cfg outer
  have compatible : s.cfg.copy.compatible s.abi.ret.layout s.abi.ret.layout = .ok true := by
    rw [source.compatible]
    simp [CompilerCovariance.compatible, CompilerCovariance.relation, CompilerCovariance.relationWithIndex,
      profile.debug, Except.mapError, bind, Except.bind, pure, Except.pure]
  have padding : s.cfg.copy.hasPadding s.abi.ret.layout = .ok true := by
    rw [source.padding]
    simp [CompilerCopy.hasPadding, metadata.unitBackend, pure, Except.pure]
  have check : s.cfg.compiler.checkPlaceType = fun _ _ _ => pure () := by
    rw [source.checkPlace]
    funext choice place value state
    simp [CompilerPlaceTypes.place, CompilerPlaceTypes.check, profile.debug,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  have computed : s.cfg.compiler.layout () 0
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      .ok s.abi.ret.layout (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) := by
    rw [dictionaries.layout]
    apply BodyQueries.local_layout s.prepared.compiler s.abi.ret.layout frames frame machine
    · apply metadata.normalizedLocal
      · simpa only [BodyStep.withUnit,LocalUnit.withUnit] using bodyIdentity
      · simpa only [BodyStep.withUnit,LocalUnit.withUnit] using body
      · simpa only [BodyStep.withUnit,LocalUnit.withUnit] using function
    · exact metadata.unitLookup
  let h := ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation s.cfg s.limits) s.limits
  have destination : h.evalPlace () ⟨0,#[]⟩ true
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      .ok (BodyStep.destination frames frame s.abi.ret.layout)
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
    apply BodyStep.evaluate_zero s.cfg.access s.cfg.allocation s.cfg.compiler
      (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation
        (ExecutionMachine.withValidation s.cfg s.limits) s.limits)) () frames frame machine
      s.abi.ret.layout metadata.unitSized
    · exact source.projection
    · exact check
    · exact computed
  have literal : h.evalOperand () (.Constant metadata.literal)
      (some s.abi.ret.layout)
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) =
      .ok ⟨.immediate .uninit,s.abi.ret.layout⟩
        (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine) := by
    change s.cfg.operands.constant ()
      metadata.literal (some s.abi.ret.layout) _ = _
    exact constant s metadata profile remaining capacity frames frame machine bodyIdentity function location
  have transfer := bound_copy_eq s s.abi.ret.layout frames frame compatible padding metadata.unitSized
  change evalRvalueIntoPlace h () _ _ _ = _
  unfold evalRvalueIntoPlace
  simp only [bind, Bind.bind, EStateM.bind, destination]
  change (h.evalOperand () (.Constant metadata.literal)
      (some s.abi.ret.layout) >>= fun op => MachineHooks.withRetagMode .Default
        (h.copyOp () op (BodyStep.destination frames frame s.abi.ret.layout))) _ = _
  simp only [bind, Bind.bind, EStateM.bind, literal]
  rw [transfer]
  exact scoped_copy s metadata profile remaining capacity positive frames frame machine noClocks noGhost shallow

 theorem statement (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (positive : 0 < s.options.limits.validation)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (bodyIdentity : frame.bodyIdentity = s.loaded.identity)
    (body : frame.body = s.loaded.body)
    (function : frame.functionInstance = s.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.stepHooks s.cfg s.limits).assign () ⟨0,#[]⟩
      (.Use (.Constant metadata.literal) .Yes)
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) machine,.ok ()) := by
  have assigned := rvalue s metadata profile remaining capacity positive frames frame machine
    bodyIdentity body function location noClocks noGhost shallow
  change MachineHooks.run (evalRvalueIntoPlace
    (ExecutionMachine.rvalueHooks (ExecutionMachine.withValidation s.cfg s.limits) s.limits)
    () (.Use (.Constant metadata.literal) .Yes) ⟨0,#[]⟩) _ = _
  simp only [MachineHooks.run, Call.run, assigned]

/-- Execute the fixed exported unit assignment through the actual source step
machine. Layout caching and the instruction pointer are the only changes. -/
 theorem step (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (positive : 0 < s.options.limits.validation)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (bodyIdentity : frame.bodyIdentity = s.loaded.identity)
    (body : frame.body = s.loaded.body)
    (function : frame.functionInstance = s.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ExecutionMachine.step s.cfg s.limits ()
      (BodyStep.current frames (BodyStep.withUnit frame .uninit none) machine) =
      (BodyStep.current frames {(BodyStep.withUnit frame .uninit (some s.abi.ret.layout)) with
        location := .mir ⟨0,1⟩} machine,.ok true) := by
  have instruction := metadata.literalStatement
  cases found : s.loaded.body.basicBlocks[0]? with
  | none => simp [found] at instruction
  | some block =>
    cases first : block.statements[0]? with
    | none => simp [found,first] at instruction
    | some stmt =>
      have kind : stmt.kind = .Assign ⟨0,#[]⟩ (.Use (.Constant metadata.literal) .Yes) := by
        simpa only [found,Option.bind_some,first,Option.map_some,Option.some.injEq] using instruction
      apply BodyStep.assignment_driver (ExecutionMachine.stepHooks s.cfg s.limits) () frames
        (BodyStep.withUnit frame .uninit none) (BodyStep.withUnit frame .uninit (some s.abi.ret.layout))
        machine block stmt ⟨0,#[]⟩ (.Use (.Constant metadata.literal) .Yes)
      · simpa only [BodyStep.withUnit,LocalUnit.withUnit] using location
      · simpa only [BodyStep.withUnit,LocalUnit.withUnit] using location
      · simpa only [BodyStep.withUnit,LocalUnit.withUnit,body] using found
      · exact first
      · exact kind
      · exact statement s metadata profile remaining capacity positive frames frame machine
          bodyIdentity body function location noClocks noGhost shallow

end EmptyFunction.BodyAssignment
