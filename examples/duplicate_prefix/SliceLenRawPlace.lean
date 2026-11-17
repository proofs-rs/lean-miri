import duplicate_prefix.SharedReferenceDeref
import duplicate_prefix.SliceLenFacts
namespace DuplicatePrefix.SliceLenRawPlace
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open CanonicalConfigFacts
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem source_local_cached
    (compiler : CompilerProviders.Prepared)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate value))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    PlaceMachine.localToOpCore (EvalPlaceConstruction.localLayout compiler) ValidityMachine.validationInProgress localId
      (Storage.withCurrent frames frame machine) =
      .ok ⟨.immediate value,layout⟩ (Storage.withCurrent frames frame machine) := by
  simp [PlaceMachine.localToOpCore,EvalPlaceConstruction.localLayout,MachineHooks.currentFrame,
    MachineHooks.afterLocalRead,ValidityMachine.validationInProgress,Storage.withCurrent,Stack.currentFrame?,
    Frame.getLocal,Frame.getLocalOperand,LocalState.access,valid,live,cached,sized,noClocks,ghost,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    Except.mapError,Except.bind,Except.pure]

theorem constructor_deref_cached_local
    (compiler : CompilerProviders.Prepared) (po : EvalPlaceConstruction.Options)
    (access : ValidityMachine.Access MiriMemoryKind RootStored) (pointers : RootPointers) (table : RootRawVTable)
    (check : Unit → MIR.Place → RuntimePlace Provenance → MachineHooks.M MiriMemoryKind Machine.RootUser Unit)
    (validate : Unit → RuntimePlace Provenance → MachineHooks.M MiriMemoryKind Machine.RootUser Unit)
    (debugOff : po.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate value))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    (EvalPlaceConstruction.compiler compiler po access pointers table check validate).deref ()
      (LocalPlaces.localRuntimePlace frames.size frame localId layout) false
      (Storage.withCurrent frames frame machine) =
      (do
        let memory ← PointerPlaceMachine.dereference access
          (CompilerExecutionProviders.pointerCompiler compiler.lifecycle.calls.symbols.facts)
          (EvalPlaceConstruction.dynamic compiler po table) table po.dynamicFuel () ⟨.immediate value,layout⟩
        pure (⟨.memory memory.mplace,memory.layout⟩ : RuntimePlace Provenance)) (Storage.withCurrent frames frame machine) := by
  have read := source_local_cached compiler frames frame machine localId value layout valid live cached sized noClocks ghost
  dsimp only [Storage.withCurrent] at read
  unfold EvalPlaceConstruction.compiler
  dsimp only
  unfold placeToOpCore
  simp [LocalPlaces.localRuntimePlace,debugOff,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,read,
    Except.mapError,Except.bind,Except.pure]
  try (rw [read];rfl)

theorem actual_deref_cached_local
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate value))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    let config := PreparedContracts.actualConfig options () remaining span
    config.projection.place.deref () (LocalPlaces.localRuntimePlace frames.size frame localId layout) false
      (Storage.withCurrent frames frame machine) =
      (do
        let memory ← config.operands.dereference () ⟨.immediate value,layout⟩
        pure (⟨.memory memory.mplace,memory.layout⟩ : RuntimePlace Provenance)) (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨po,pointers,table,compilerEq,projectionEq,operandEq⟩ := fields.placeConstruction
  have poDebug : po.debugAssertions = false := by
    have debug := fields.debug.trans debugOff
    rw [compilerEq] at debug
    exact debug
  have staged := constructor_deref_cached_local PreparedReflection.actual.compiler po config.access pointers table
    config.compiler.checkPlaceType config.compiler.validate poDebug frames frame machine localId value layout
    valid live cached sized noClocks ghost
  change config.projection.place.deref () _ false _ = _
  rw [projectionEq]
  change config.compiler.deref () _ false _ = _
  rw [compilerEq]
  rw [operandEq,projectionEq]
  exact staged

theorem eval_one_deref
    (projection : PlaceProjectionHooks Provenance RootState Unit MachineHooks.FrameExtra)
    (localId : Miri.MIR.LocalId) (localPlace : RuntimePlace Provenance) (state : RootState)
    (read : localToPlace projection.place () localId state = .ok localPlace state)
    (check : ∀ value after, projection.place.checkPlaceType () ⟨localId,#[.Deref]⟩ value after = .ok () after) :
    PlaceDynamic.evalPlace projection () ⟨localId,#[.Deref]⟩ false state =
      projection.place.deref () localPlace false state := by
  unfold PlaceDynamic.evalPlace
  simp only [read,bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Bool.false_and,ite_false,
    ← Array.forIn_toList,List.forIn_cons,List.forIn_nil,PlaceDynamic.project]
  cases result : projection.place.deref () localPlace false state with
  | error error after => simp [result,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  | ok value after => simp [result,check,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]

theorem actual_eval_deref_cached_local
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate value))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    let config := PreparedContracts.actualConfig options () remaining span
    (ExecutionMachine.rvalueHooks config limits).evalPlace () ⟨localId,#[.Deref]⟩ false
      (Storage.withCurrent frames frame machine) =
      (do
        let memory ← config.operands.dereference () ⟨.immediate value,layout⟩
        pure (⟨.memory memory.mplace,memory.layout⟩ : RuntimePlace Provenance)) (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let projection := ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)
  let state := Storage.withCurrent frames frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have getFrame : projection.place.getFrame state = .ok frame state := by
    change config.projection.place.getFrame state = _
    rw [fields.projectionGetFrame]
    exact Storage.current_frame frames frame machine
  have index : projection.place.frameIndex state = .ok frames.size state := by
    change config.projection.place.frameIndex state = _
    rw [fields.projectionFrameIndex]
    simp [state,Storage.withCurrent,Stack.frameIndex,Array.isEmpty_push,
      get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Except.pure,Except.bind]
  have localRead := LocalPlaces.localToPlace_cached projection.place () frame localId frames.size layout state
    valid getFrame index cached sized
  have check := RootLocalStages.place_check_skipped options limits () remaining span debugOff ⟨localId,#[.Deref]⟩
  have evaluated := eval_one_deref projection localId (LocalPlaces.localRuntimePlace frames.size frame localId layout) state localRead check
  change PlaceDynamic.evalPlace projection () ⟨localId,#[.Deref]⟩ false state = _
  rw [evaluated]
  exact actual_deref_cached_local options remaining span debugOff frames frame machine localId value layout valid live cached sized noClocks ghost

#print axioms actual_eval_deref_cached_local

theorem actual_shared_not_raw
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) :
    (PreparedContracts.actualConfig options () remaining span).isRawPointer () 7 = pure false := by
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).isRawPointer]
  funext state
  dsimp only
  with_unfolding_all rfl

theorem actual_place_base_reference
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = SliceLenFacts.body.body) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).placeBaseRaw ()
      ⟨1,#[.Deref]⟩ (Storage.withCurrent frames frame machine) =
      .ok false (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  change (do
    let frame ← MachineHooks.currentFrame
    let some ty := frame.body.locals[1]? | throw (StepError.invalidProgram "raw place base local missing")
    config.isRawPointer () ty) (Storage.withCurrent frames frame machine) = _
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,Bind.bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,Pure.pure,EStateM.pure]
  rw [sourceBody]
  with_unfolding_all change config.isRawPointer () 7 (Storage.withCurrent frames frame machine) = _
  exact congrFun (actual_shared_not_raw options remaining span) (Storage.withCurrent frames frame machine)

#print axioms actual_place_base_reference

#print axioms actual_deref_cached_local

#print axioms constructor_deref_cached_local
end
end DuplicatePrefix.SliceLenRawPlace
