import duplicate_prefix.PrimitiveCallReturn
namespace DuplicatePrefix.CallLocalRead
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem place_to_op_cached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : Miri.MIR.LocalId) (layout : LocalLayout) (value : Immediate Provenance)
    (valid : id < frame.locals.size)
    (live : frame.locals[id].value = .live (.immediate value))
    (cached : frame.locals[id].layout = some layout)
    (sized : layout.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).placeToOp ()
      (LocalPlaces.localRuntimePlace frames.size frame id layout).stackView (Storage.withCurrent frames frame machine) =
      .ok ⟨.immediate value,layout⟩ (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have read : config.projection.place.localToOp () id (Storage.withCurrent frames frame machine) =
      .ok ⟨.immediate value,layout⟩ (Storage.withCurrent frames frame machine) := by
    rw [fields.projectionLocalToOp]
    exact GenericCallReturn.cached_local_read (ValidityMachine.compilerPolicy config.compiler) ()
      frames frame machine id layout value valid live cached sized noClocks rfl ghost
  unfold ExecutionMachine.callHooks ExecutionCalls.make
  dsimp only
  change placeToOp (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place () _ _ = _
  unfold placeToOp
  change placeToOpCore _ config.projection.place.debugAssertions config.projection.place.frameIndex config.projection.place.localToOp _ () _ _ = _
  unfold placeToOpCore
  rw [fields.projectionFrameIndex,fields.projectionDebug,debugOff]
  simp [RuntimePlace.stackView,RuntimeStackPlace.toRuntimePlace,LocalPlaces.localRuntimePlace,
    Stack.frameIndex,Storage.withCurrent,Array.isEmpty_push,read,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Except.pure]

  dsimp only [Storage.withCurrent] at read
  rw [read]

#print axioms place_to_op_cached
end DuplicatePrefix.CallLocalRead
