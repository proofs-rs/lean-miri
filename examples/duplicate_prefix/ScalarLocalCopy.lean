import duplicate_prefix.ActualLocalCopy
import duplicate_prefix.RootPointerCopy
import duplicate_prefix.RootUsizeWrite
namespace DuplicatePrefix.ScalarLocalCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem pointer
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceId destId : Miri.MIR.LocalId) (value : Scalar Provenance)
    (different : destId ≠ sourceId)
    (valid1 : sourceId < frame.locals.size) (valid2 : destId < frame.locals.size)
    (live1 : frame.locals[sourceId].value = .live (.immediate (.scalar value)))
    (cached1 : frame.locals[sourceId].layout = some CopyCompilerFacts.destPointerLayout)
    (live2 : frame.locals[destId].value = .live (.immediate .uninit))
    (uncached2 : frame.locals[destId].layout = none)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler destId
      (Storage.withCurrent framesBefore frame machine) = .ok CopyCompilerFacts.destPointerLayout (Storage.withCurrent framesBefore frame machine))
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Use (.Copy ⟨sourceId,#[]⟩) .Yes) ⟨destId,#[]⟩ (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (ActualLocalCopy.written frame destId CopyCompilerFacts.destPointerLayout valid2 (.scalar value)) machine) := by
  refine ActualLocalCopy.uncached_of_copy options limits remaining span debugOff framesBefore frame machine
    sourceId destId CopyCompilerFacts.destPointerLayout (.scalar value) different RootRawPointerValidity.mut_pointer_sized valid1 valid2 live1 cached1 uncached2
    query noClocks tracker tracked defaultMode ghostFalse ?_
  let cached := LocalPlaces.cachePlaceLayout frame destId CopyCompilerFacts.destPointerLayout valid2
  have valid : destId < cached.locals.size := by simpa [cached,LocalPlaces.cachePlaceLayout] using valid2
  have live : cached.locals[destId].value = .live (.immediate .uninit) := by
    simpa [cached,LocalPlaces.cachePlaceLayout] using live2
  have cache : cached.locals[destId].layout = some CopyCompilerFacts.destPointerLayout := by
    simp [cached,LocalPlaces.cachePlaceLayout]
  exact RootPointerCopy.copy_mut_pointer_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore cached machine destId .uninit value valid live cache noClocks ghostFalse shallow

theorem const_pointer
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceId destId : Miri.MIR.LocalId) (value : Scalar Provenance)
    (different : destId ≠ sourceId)
    (valid1 : sourceId < frame.locals.size) (valid2 : destId < frame.locals.size)
    (live1 : frame.locals[sourceId].value = .live (.immediate (.scalar value)))
    (cached1 : frame.locals[sourceId].layout = some CopyCompilerFacts.sourcePointerLayout)
    (live2 : frame.locals[destId].value = .live (.immediate .uninit))
    (uncached2 : frame.locals[destId].layout = none)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler destId
      (Storage.withCurrent framesBefore frame machine) = .ok CopyCompilerFacts.sourcePointerLayout (Storage.withCurrent framesBefore frame machine))
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Use (.Copy ⟨sourceId,#[]⟩) .Yes) ⟨destId,#[]⟩ (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (ActualLocalCopy.written frame destId CopyCompilerFacts.sourcePointerLayout valid2 (.scalar value)) machine) := by
  refine ActualLocalCopy.uncached_of_copy options limits remaining span debugOff framesBefore frame machine
    sourceId destId CopyCompilerFacts.sourcePointerLayout (.scalar value) different RootRawPointerValidity.const_pointer_sized valid1 valid2 live1 cached1 uncached2
    query noClocks tracker tracked defaultMode ghostFalse ?_
  let cached := LocalPlaces.cachePlaceLayout frame destId CopyCompilerFacts.sourcePointerLayout valid2
  have valid : destId < cached.locals.size := by simpa [cached,LocalPlaces.cachePlaceLayout] using valid2
  have live : cached.locals[destId].value = .live (.immediate .uninit) := by
    simpa [cached,LocalPlaces.cachePlaceLayout] using live2
  have cache : cached.locals[destId].layout = some CopyCompilerFacts.sourcePointerLayout := by
    simp [cached,LocalPlaces.cachePlaceLayout]
  exact RootPointerCopy.copy_const_pointer_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore cached machine destId .uninit value valid live cache noClocks ghostFalse shallow

theorem usize
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceId destId : Miri.MIR.LocalId) (count : UInt64)
    (different : destId ≠ sourceId)
    (valid1 : sourceId < frame.locals.size) (valid2 : destId < frame.locals.size)
    (live1 : frame.locals[sourceId].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cached1 : frame.locals[sourceId].layout = some RootCompilerFacts.usizeLayout)
    (live2 : frame.locals[destId].value = .live (.immediate .uninit))
    (uncached2 : frame.locals[destId].layout = none)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler destId
      (Storage.withCurrent framesBefore frame machine) = .ok RootCompilerFacts.usizeLayout (Storage.withCurrent framesBefore frame machine))
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Use (.Copy ⟨sourceId,#[]⟩) .Yes) ⟨destId,#[]⟩ (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore (ActualLocalCopy.written frame destId RootCompilerFacts.usizeLayout valid2 (.scalar (.fromScalarInt (.ofUInt64 count)))) machine) := by
  refine ActualLocalCopy.uncached_of_copy options limits remaining span debugOff framesBefore frame machine
    sourceId destId RootCompilerFacts.usizeLayout (.scalar (.fromScalarInt (.ofUInt64 count))) different ActualScalarCopy.usize_sized valid1 valid2 live1 cached1 uncached2
    query noClocks tracker tracked defaultMode ghostFalse ?_
  let cached := LocalPlaces.cachePlaceLayout frame destId RootCompilerFacts.usizeLayout valid2
  have valid : destId < cached.locals.size := by simpa [cached,LocalPlaces.cachePlaceLayout] using valid2
  have live : cached.locals[destId].value = .live (.immediate .uninit) := by
    simpa [cached,LocalPlaces.cachePlaceLayout] using live2
  have cache : cached.locals[destId].layout = some RootCompilerFacts.usizeLayout := by
    simp [cached,LocalPlaces.cachePlaceLayout]
  dsimp only
  rw [ActualScalarCopy.actual_copy_usize options limits (remaining+1) span debugOff count _ rfl]
  exact RootUsizeWrite.write_usize_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore cached machine destId .uninit (.ofUInt64 count) valid live cache noClocks ghostFalse shallow

#print axioms pointer
#print axioms const_pointer
#print axioms usize
end DuplicatePrefix.ScalarLocalCopy
