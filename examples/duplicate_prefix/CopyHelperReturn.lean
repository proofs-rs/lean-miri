import duplicate_prefix.CopyHelperUnit
import duplicate_prefix.CopyHelperFacts
import duplicate_prefix.PrimitiveCallReturn
namespace DuplicatePrefix.CopyHelperReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem copy_unit_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance)
    (valid : localId < caller.locals.size)
    (live : caller.locals[localId].value = .live (.immediate old))
    (cached : caller.locals[localId].layout = some CopyHelperUnit.layout)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller localId CopyHelperUnit.layout) :
    (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyReturn ()
      ⟨.immediate .uninit, CopyHelperUnit.layout⟩ view
      (Storage.withCurrent frames caller machine) =
      (Storage.withCurrent frames {caller with locals := (caller.locals.set localId
        {value := .live (.immediate .uninit),
         layout := caller.locals[localId].layout} valid)} machine, .ok ()) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let bound := ExecutionMachine.withValidation config limits
  let place := (ExecutionMachine.projectionHooks bound).place
  let dest := LocalPlaces.localRuntimePlace frames.size caller localId CopyHelperUnit.layout
  let value : Immediate Provenance := Immediate.uninit
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have compatible : bound.copy.compatible = CompilerCovariance.compatible PreparedReflection.actual.compiler false := by
    change config.copy.compatible = _
    rw [fields.copyCompatible, debugOff]
  have flag := GenericCallReturn.same_layout_transmute_flag place bound.copy PreparedReflection.actual.compiler ()
    CopyHelperUnit.layout value dest rfl compatible
  have exactCopy : copyRuntimePlace place bound.copy () ⟨.immediate value, CopyHelperUnit.layout⟩ dest true =
      (ExecutionMachine.rvalueHooks config limits).copyOp () ⟨.immediate value, CopyHelperUnit.layout⟩ dest := by
    rw [flag]
    rfl
  have copy := CopyHelperUnit.copy_unit_reduction options limits (remaining + 1) span debugOff dest rfl
  have write := CopyHelperUnit.write_unit_shallow options limits remaining span debugOff fuel validationFuel
    frames caller machine localId old valid live cached noClocks ghost shallow
  change MachineHooks.run (copyRuntimePlace place bound.copy ()
    ⟨.immediate value, CopyHelperUnit.layout⟩ view.toRuntimePlace true) _ = _
  rw [destination, exactCopy, copy]
  unfold MachineHooks.run Call.run
  rw [write]

theorem read_unit_return_uncached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (valid : (0 : MIR.LocalId) < frame.locals.size)
    (live : frame.locals[0].value = .live (.immediate .uninit))
    (uncached : frame.locals[0].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () remaining span) limits).returnOperand ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (LocalOperands.cachedLayoutFrame frame 0 CopyHelperUnit.layout valid) machine,
        .ok ⟨.immediate .uninit,CopyHelperUnit.layout⟩) := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have query := PointerAddFacts.compute_local frames frame machine 0 2 CopyHelperUnit.layout
    (CopyHelperFacts.normalized_local0 frame sourceBody identity callee) CopyHelperUnit.layout_query
  have queryConcrete := query
  simp only [Storage.withCurrent] at queryConcrete
  have read : PlaceMachine.localToOp (ValidityMachine.compilerPolicy config.compiler) () 0
      (Storage.withCurrent frames frame machine) =
      .ok ⟨.immediate .uninit,CopyHelperUnit.layout⟩
        (Storage.withCurrent frames (LocalOperands.cachedLayoutFrame frame 0 CopyHelperUnit.layout valid) machine) := by
    unfold PlaceMachine.localToOp PlaceMachine.localToOpCore PlaceMachine.layoutLocal
    simp only [ValidityMachine.compilerPolicy]
    rw [fields.layout]
    simp [MachineHooks.currentFrame,MachineHooks.setCurrentFrame,MachineHooks.afterLocalRead,
      Storage.withCurrent,Stack.currentFrame?,Frame.getLocal,Frame.getLocalOperand,
      Frame.getOrCacheLocalLayout,LocalState.access,valid,live,uncached,queryConcrete,
      CopyHelperUnit.layout_shape.2.1,noClocks,ValidityMachine.validationInProgress,
      ghost,LocalOperands.cachedLayoutFrame,bind,EStateM.bind,get,getThe,MonadStateOf.get,
      EStateM.get,set,MonadStateOf.set,EStateM.set,pure,EStateM.pure,Except.pure,Except.bind,Except.mapError]
  change MachineHooks.run (config.projection.place.localToOp () 0) _ = _
  rw [fields.projectionLocalToOp]
  unfold MachineHooks.run Call.run
  rw [read]

#print axioms copy_unit_return
open Lean Elab Command in
run_cmd do
  for declaration in [``copy_unit_return, ``read_unit_return_uncached] do
   for dependency in (← collectAxioms declaration) do
     unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
       throwError "unapproved axiom {dependency}"
end DuplicatePrefix.CopyHelperReturn
