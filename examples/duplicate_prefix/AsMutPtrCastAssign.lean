import duplicate_prefix.AsMutPtrCast
import duplicate_prefix.ActualLocalCopy
import duplicate_prefix.AsMutPtrLayouts
import duplicate_prefix.ActualLocalPlace
namespace DuplicatePrefix.AsMutPtrCastAssign
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem move_cached_local
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (value : Immediate Provenance) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate value))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.backendRepr.isUnsized = false)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).evalOperandAt
      () (OperandPath.rvalue "operand") (.Move ⟨localId,#[]⟩) none (Storage.withCurrent frames frame machine) =
      .ok ⟨.immediate value,layout⟩ (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () remaining span
  let hooks := ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits)
  let state := Storage.withCurrent frames frame machine
  have validationGetter : hooks.compiler.validationInProgress state = .ok false state := by
    change config.compiler.validationInProgress state = _
    rw [(CanonicalConfigFacts.actual_fields options () remaining span).compilerValidationInProgress]
    simp [ValidityMachine.validationInProgress,state,Storage.withCurrent,ghost,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  have read := LocalOperands.cached_immediate hooks () frames frame machine localId value layout none
    valid live cached sized noClocks false validationGetter
  have check := RootLocalStages.operand_check_skipped options limits () remaining span debugOff
    (OperandDispatch.wholeLocal localId) ⟨.immediate value,layout⟩ state
  exact OperandDispatch.evalOperandAt_move_wholeLocal hooks () (OperandPath.rvalue "operand")
    localId none state state _ read check

theorem actual_cast_assignment
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer Provenance) (len : UInt64)
    (valid2 : (2 : Miri.MIR.LocalId) < frame.locals.size)
    (valid3 : (3 : Miri.MIR.LocalId) < frame.locals.size)
    (live2 : frame.locals[2].value = .live (.immediate .uninit))
    (uncached2 : frame.locals[2].layout = none)
    (live3 : frame.locals[3].value = .live (.immediate
      (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        pointer len AsMutPtrFacts.rawLayout).imm))
    (cached3 : frame.locals[3].layout = some AsMutPtrFacts.rawLayout)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (location : frame.location = .mir ⟨0,5⟩)
    (noClocks : frame.extra.dataRace = none) (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks cfg limits) ()
      (.Cast .PtrToPtr (.Move ⟨3,#[]⟩) 8) ⟨2,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (ActualLocalCopy.written frame 2 CopyCompilerFacts.destPointerLayout valid2
        (.scalar (Scalar.fromPointer cfg.access.runtime.base pointer))) machine) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks cfg limits
  let cached := LocalPlaces.cachePlaceLayout frame 2 CopyCompilerFacts.destPointerLayout valid2
  let state := Storage.withCurrent frames cached machine
  have query := AsMutPtrLayouts.compute frames frame machine body identity callee 2 (Or.inr (Or.inl rfl))
  have query' : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 2
      (Storage.withCurrent frames frame machine) = .ok CopyCompilerFacts.destPointerLayout (Storage.withCurrent frames frame machine) := by
    simpa only [show (2 : Miri.MIR.LocalId) = 2 from rfl,or_true,ite_true] using query
  have dest := ActualLocalPlace.uncached options limits (remaining+1) span debugOff frames frame machine
    2 CopyCompilerFacts.destPointerLayout valid2 uncached2 (by decide +kernel) query'
  have valid3' : (3 : Miri.MIR.LocalId) < cached.locals.size := by simpa [cached,LocalPlaces.cachePlaceLayout] using valid3
  have live3' : cached.locals[3].value = .live (.immediate
      (RetagReferencePlace.sliceValue cfg.access.runtime.base pointer len AsMutPtrFacts.rawLayout).imm) := by
    simpa [cached,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live3
  have cache3' : cached.locals[3].layout = some AsMutPtrFacts.rawLayout := by
    simpa [cached,LocalPlaces.cachePlaceLayout,Array.getElem_set] using cached3
  have operand := move_cached_local options limits (remaining+1) span debugOff frames cached machine 3
    (RetagReferencePlace.sliceValue cfg.access.runtime.base pointer len AsMutPtrFacts.rawLayout).imm AsMutPtrFacts.rawLayout
    valid3' live3' cache3' (by simpa [LayoutData.isSized,BackendRepr.isSized] using AsMutPtrFacts.raw_sized) noClocks ghost
  have normalized := AsMutPtrLayouts.normalize_cast options (remaining+1) span frames cached machine body identity callee location
  have valid2' : (2 : Miri.MIR.LocalId) < cached.locals.size := by simpa [cached,LocalPlaces.cachePlaceLayout] using valid2
  have live2' : cached.locals[2].value = .live (.immediate .uninit) := by simpa [cached,LocalPlaces.cachePlaceLayout] using live2
  have cache2' : cached.locals[2].layout = some CopyCompilerFacts.destPointerLayout := by simp [cached,LocalPlaces.cachePlaceLayout]
  have cast := AsMutPtrCast.actual_cast_write_cached options limits remaining span debugOff fuel validationFuel
    frames cached machine 2 .uninit pointer len valid2' live2' cache2' noClocks ghost shallow
  unfold evalRvalueIntoPlace
  simp only [bind,Bind.bind,EStateM.bind]
  rw [dest]
  simp only
  rw [operand]
  simp only
  change (do let ty ← cfg.rvalues.normalize () 8
             hooks.cast () ⟨.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base pointer len AsMutPtrFacts.rawLayout).imm,AsMutPtrFacts.rawLayout⟩ .PtrToPtr ty
               (LocalPlaces.localRuntimePlace frames.size cached 2 CopyCompilerFacts.destPointerLayout)) state = _
  simp only [bind,Bind.bind,EStateM.bind]
  have normalized' : cfg.rvalues.normalize () 8 state = .ok 8 state := normalized
  rw [normalized']
  simpa only [ActualLocalCopy.written,cached] using cast

#print axioms actual_cast_assignment
end DuplicatePrefix.AsMutPtrCastAssign
