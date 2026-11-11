import empty_function.ProjectedImmediateForce
import empty_function.ProjectedCopy
namespace EmptyFunction.ProjectedForceTotal
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- The actual projection propagates a failed parent allocation, including its
partially changed state, before old-value writing or caller-slot replacement. -/
theorem allocation_error {K U C : Type} [DecidableEq K]
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C) (choice : C)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout) (base target : LocalLayout)
    (value : Immediate Provenance)
    (atSlot : frame.locals[id]? = some slot)
    (live : slot.value = .live (.immediate value)) (cache : slot.layout = some base)
    (sized : base.layout.isSized = true) (debugOff : compiler.debugAssertions = false)
    (error : StepError) (failed : MachineHooks.State K (ValidityMachine.UserState U))
    (created : PlaceMachine.allocateStack allocation base (LocalUnit.current frames frame machine) =
      .error error failed)
    (offset : Option Size) (identity : LocalsIdentity) :
    forceAllocation (ValidityMachine.placeHooks access allocation compiler) choice
      ⟨.local frames.size id offset identity,target⟩ (LocalUnit.current frames frame machine) =
      .error error failed := by
  have got := EmptyFunction.LocalImmediate.get_local frame id slot atSlot
  have old : frame.getLocalOperand id = .ok (.immediate value) := by
    simp [Frame.getLocalOperand,got,LocalState.access,live,Except.mapError,
      bind,Except.bind,pure,Except.pure]
  have layout : placeLayoutOfLocal (ValidityMachine.placeHooks access allocation compiler) choice id
      (LocalUnit.current frames frame machine) = .ok base (LocalUnit.current frames frame machine) := by
    simp [placeLayoutOfLocal,ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
      MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,got,cache,get,getThe,MonadStateOf.get,EStateM.get,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Except.pure]
  unfold forceAllocation
  dsimp only
  rw [requireCurrent_eq,checkLocalIdentity_debugOff _ identity debugOff]
  simp only [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
    Stack.frameIndex,MachineHooks.currentFrame,LocalUnit.current,Stack.currentFrame?,got,old,
    Array.isEmpty_push,Array.size_push,Array.back?_push,Nat.add_sub_cancel,
    beq_self_eq_true,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    Except.pure,stackLift_ok]
  simp only [LocalUnit.current] at created layout
  erw [layout]
  simp only [sized,Bool.not_true,Bool.false_eq_true,↓reduceIte,bind,Bind.bind,EStateM.bind]
  rw [created]
/-- A parent-allocation failure reaches the actual Return copy callback with
its original error and failed state. No validation or caller-slot update follows. -/
theorem copy_error_from_force (s : EmptyFunction.WholeCall.Static)
    (metadata : EmptyFunction.Specification.Metadata s) (profile : EmptyFunction.Specification.Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (state failed : EmptyFunction.WholeCall.State) (index : Nat) (id : MIR.LocalId)
    (offset : Size) (identity : LocalsIdentity) (error : StepError)
    (forced : forceAllocation s.cfg.projection.place ()
      ⟨.local index id (some offset) identity,s.abi.ret.layout⟩ state = .error error failed) :
    (EmptyFunction.ReturnStep.control s).copyReturn () ⟨.immediate .uninit,s.abi.ret.layout⟩
      (.frameLocal index id (some offset) s.abi.ret.layout identity) state =
      (failed,.error error) := by
  let leaves := EmptyFunction.Configuration.leaves s.prepared s.options.place.debugAssertions
  have built : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options) leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [EmptyFunction.Configuration.rootConfig,capacity,Nat.add_assoc] using s.built
  have fields := EmptyFunction.BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    leaves (remaining+1) metadata.construction s.cfg built
  have compatible : s.cfg.copy.compatible s.abi.ret.layout s.abi.ret.layout = .ok true := by
    rw [fields.compatible]
    simp [CompilerCovariance.compatible,CompilerCovariance.relation,CompilerCovariance.relationWithIndex,
      profile.debug,Except.mapError,bind,Except.bind,pure,Except.pure]
  have padding : s.cfg.copy.hasPadding s.abi.ret.layout = .ok true := by
    rw [fields.padding]
    simp [CompilerCopy.hasPadding,metadata.unitBackend,pure,Except.pure]
  have copied : copyRuntimePlaceNoValidate s.cfg.projection.place s.cfg.copy ()
      ⟨.immediate .uninit,s.abi.ret.layout⟩ ⟨.local index id (some offset) identity,s.abi.ret.layout⟩ true state =
      .error error failed := by
    simp only [copyRuntimePlaceNoValidate,compatible,placeLift_ok,padding,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,metadata.unitSized,
      Bool.not_true,Bool.false_and,Bool.false_or,Bool.false_eq_true,↓reduceIte,bne_self_eq_false]
    unfold writePlaceImmediateNoValidate asMplaceOrMutableLocal
    simp only [metadata.unitSized,Bool.not_true,Bool.false_eq_true,↓reduceIte,
      Option.isSome_some,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,forced]
  have complete : copyRuntimePlace s.cfg.projection.place s.cfg.copy ()
      ⟨.immediate .uninit,s.abi.ret.layout⟩ ⟨.local index id (some offset) identity,s.abi.ret.layout⟩ true state =
      .error error failed := by
    simp only [copyRuntimePlace,bind,Bind.bind,EStateM.bind,copied]
  have boundCopy : copyRuntimePlace (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation s.cfg s.limits)).place
      (ExecutionMachine.withValidation s.cfg s.limits).copy () ⟨.immediate .uninit,s.abi.ret.layout⟩
      ⟨.local index id (some offset) identity,s.abi.ret.layout⟩ true =
      copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,s.abi.ret.layout⟩
        ⟨.local index id (some offset) identity,s.abi.ret.layout⟩ true := by
    funext before
    simp [ExecutionMachine.withValidation,ExecutionMachine.projectionHooks,TypedMachineBindings.bindValidation,
      copyRuntimePlace,copyRuntimePlaceNoValidate,compatible,padding,metadata.unitSized,
      bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  change MachineHooks.run (copyRuntimePlace _ _ () _ _ true) state = _
  simp only [RuntimeStackPlace.toRuntimePlace]
  rw [boundCopy]
  simp only [MachineHooks.run,Call.run,complete]
end EmptyFunction.ProjectedForceTotal
