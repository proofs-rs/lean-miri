import duplicate_prefix.CopyHelperStages
import duplicate_prefix.CopyHelperIntrinsic
import duplicate_prefix.SourceSteps
namespace DuplicatePrefix.CopyHelperSteps
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def advance (frame : CompilerFrameContext.ActualFrame) (location : Location) :=
  {frame with location := .mir {location with statementIndex := location.statementIndex+1}}

theorem assign_of_actual_rvalue
    (config : ExecutionMachine.Config MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
    (limits : ExecutionMachine.Limits)
    (frames : Array CompilerFrameContext.ActualFrame) (frame afterFrame : CompilerFrameContext.ActualFrame)
    (machine afterMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (location : Location) (place : Place) (value : Rvalue)
    (located : frame.location = .mir location)
    (afterLocated : afterFrame.location = .mir location)
    (source : CopyPreconditions.Bodies.statementKindAt frame.body location.block location.statementIndex = some (.Assign place value))
    (actual : evalRvalueIntoPlace (ExecutionMachine.rvalueHooks config limits) () value place
      (Storage.withCurrent frames frame machine) = .ok () (Storage.withCurrent frames afterFrame afterMachine)) :
    ExecutionMachine.step config limits () (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (advance afterFrame location) afterMachine,.ok true) := by
  cases blockAt : frame.body.basicBlocks[location.block]? with
  | none => simp [CopyPreconditions.Bodies.statementKindAt,blockAt] at source
  | some block =>
    cases stmtAt : block.statements[location.statementIndex]? with
    | none => simp [CopyPreconditions.Bodies.statementKindAt,blockAt,stmtAt] at source
    | some statement =>
      have kind : statement.kind = .Assign place value := by
        simpa [CopyPreconditions.Bodies.statementKindAt,blockAt,stmtAt] using source
      have effect : Step.evalStatement (ExecutionMachine.stepHooks config limits) () statement
          (Storage.withCurrent frames frame machine) =
          (Storage.withCurrent frames afterFrame afterMachine,.ok ()) := by
        unfold Step.evalStatement
        simp only [kind]
        rw [StepAssembly.assign]
        unfold MachineHooks.run Call.run
        rw [actual]
      have result := StepFacts.step_statement (ExecutionMachine.stepHooks config limits) ()
        (Storage.withCurrent frames frame machine) (Storage.withCurrent frames afterFrame afterMachine)
        frame afterFrame location location block statement
        (by simp [Storage.withCurrent,Stack.currentFrame?]) located blockAt stmtAt effect
        (by simp [Storage.withCurrent]) (by simp [Storage.withCurrent,Stack.currentFrame?]) afterLocated
        (by simp [Storage.withCurrent])
      simpa [ExecutionMachine.step,Storage.withCurrent,advance,Array.set_push] using result


theorem source_copy_step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (value : Scalar Provenance)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (validSource : (1 : MIR.LocalId) < frame.locals.size)
    (validDest : (14 : MIR.LocalId) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (.scalar value)))
    (sourceCached : frame.locals[1].layout = some CopyCompilerFacts.sourcePointerLayout)
    (destLive : frame.locals[14].value = .live (.immediate .uninit))
    (destUncached : frame.locals[14].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (location : frame.location = .mir ⟨7,3⟩) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore
        (advance (ActualLocalCopy.written frame 14 CopyCompilerFacts.sourcePointerLayout validDest (.scalar value)) ⟨7,3⟩) machine,.ok true) := by
  apply assign_of_actual_rvalue (PreparedContracts.actualConfig options () (remaining+1) span) limits
    framesBefore frame (ActualLocalCopy.written frame 14 CopyCompilerFacts.sourcePointerLayout validDest (.scalar value)) machine machine
    ⟨7,3⟩ ⟨14,#[]⟩ (.Use (.Copy ⟨1,#[]⟩) .Yes) location
  · simpa [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using location
  · rw [sourceBody]
    exact CopyHelperFacts.source_copy_statement
  · exact CopyHelperStages.source_copy options limits remaining span debugOff fuel validationFuel
      framesBefore frame machine value sourceBody identity callee validSource validDest sourceLive sourceCached
      destLive destUncached noClocks tracker tracked defaultMode ghostFalse shallow

theorem destination_copy_step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (value : Scalar Provenance)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (validSource : (2 : MIR.LocalId) < frame.locals.size)
    (validDest : (15 : MIR.LocalId) < frame.locals.size)
    (sourceLive : frame.locals[2].value = .live (.immediate (.scalar value)))
    (sourceCached : frame.locals[2].layout = some CopyCompilerFacts.destPointerLayout)
    (destLive : frame.locals[15].value = .live (.immediate .uninit))
    (destUncached : frame.locals[15].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (location : frame.location = .mir ⟨7,5⟩) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore
        (advance (ActualLocalCopy.written frame 15 CopyCompilerFacts.destPointerLayout validDest (.scalar value)) ⟨7,5⟩) machine,.ok true) := by
  apply assign_of_actual_rvalue (PreparedContracts.actualConfig options () (remaining+1) span) limits
    framesBefore frame (ActualLocalCopy.written frame 15 CopyCompilerFacts.destPointerLayout validDest (.scalar value)) machine machine
    ⟨7,5⟩ ⟨15,#[]⟩ (.Use (.Copy ⟨2,#[]⟩) .Yes) location
  · simpa [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using location
  · rw [sourceBody]
    exact CopyHelperFacts.destination_copy_statement
  · exact CopyHelperStages.destination_copy options limits remaining span debugOff fuel validationFuel
      framesBefore frame machine value sourceBody identity callee validSource validDest sourceLive sourceCached
      destLive destUncached noClocks tracker tracked defaultMode ghostFalse shallow

theorem count_copy_step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (value : UInt64)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (validSource : (3 : MIR.LocalId) < frame.locals.size)
    (validDest : (16 : MIR.LocalId) < frame.locals.size)
    (sourceLive : frame.locals[3].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 value)))))
    (sourceCached : frame.locals[3].layout = some RootCompilerFacts.usizeLayout)
    (destLive : frame.locals[16].value = .live (.immediate .uninit))
    (destUncached : frame.locals[16].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (location : frame.location = .mir ⟨7,7⟩) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore
        (advance (ActualLocalCopy.written frame 16 RootCompilerFacts.usizeLayout validDest (.scalar (.fromScalarInt (.ofUInt64 value)))) ⟨7,7⟩) machine,.ok true) := by
  apply assign_of_actual_rvalue (PreparedContracts.actualConfig options () (remaining+1) span) limits
    framesBefore frame (ActualLocalCopy.written frame 16 RootCompilerFacts.usizeLayout validDest (.scalar (.fromScalarInt (.ofUInt64 value)))) machine machine
    ⟨7,7⟩ ⟨16,#[]⟩ (.Use (.Copy ⟨3,#[]⟩) .Yes) location
  · simpa [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using location
  · rw [sourceBody]
    exact CopyHelperFacts.count_copy_statement
  · exact CopyHelperStages.count_copy options limits remaining span debugOff fuel validationFuel
      framesBefore frame machine value sourceBody identity callee validSource validDest sourceLive sourceCached
      destLive destUncached noClocks tracker tracked defaultMode ghostFalse shallow
theorem unit_assignment_step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (old : Immediate Provenance)
    (valid : 4 < frame.locals.size)
    (live : frame.locals[4].value = .live (.immediate old))
    (uncached : frame.locals[4].layout = none)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (location : frame.location = .mir ⟨6,0⟩)
    (fnInstance : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore
        (advance (ActualLocalCopy.written frame 4 CopyHelperUnit.layout valid .uninit) ⟨6,0⟩) machine,.ok true) := by
  have query := CopyHelperFacts.actual_unit_query framesBefore frame machine sourceBody identity fnInstance
  apply assign_of_actual_rvalue (PreparedContracts.actualConfig options () (remaining+1) span) limits
    framesBefore frame (ActualLocalCopy.written frame 4 CopyHelperUnit.layout valid .uninit) machine machine
    ⟨6,0⟩ ⟨4,#[]⟩ (.Use (.Constant CopyHelperConstant.constant) .Yes) location
  · simpa [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using location
  · rw [sourceBody]
    with_unfolding_all rfl
  · exact CopyHelperConstant.assign_unit_uncached options limits remaining span source debugOff fuel validationFuel
      framesBefore frame machine 4 old valid live uncached query
      (congrArg (fun i : BodyIdentity => i.index) identity) location fnInstance noClocks
      tracker tracked defaultMode ghostFalse shallow

theorem storage_live
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (location : Location) (id : MIR.LocalId) (ty : TyId)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (located : frame.location = .mir location)
    (source : CopyPreconditions.Bodies.statementKindAt HelperCompilerFacts.copyBody.body location.block location.statementIndex = some (.StorageLive id))
    (typed : HelperCompilerFacts.copyBody.body.locals[id]? = some ty)
    (trivial : CompilerStorage.veryTriviallySized PreparedReflection.actual.compiler.runtime ty = .ok true)
    (valid : id < frame.locals.size) (dead : frame.locals[id].value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () remaining span) limits ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (SourceSteps.liveFrame frame location id valid) machine,.ok true) := by
  cases blockAt : HelperCompilerFacts.copyBody.body.basicBlocks[location.block]? with
  | none => simp [CopyPreconditions.Bodies.statementKindAt,blockAt] at source
  | some block =>
    cases stmtAt : block.statements[location.statementIndex]? with
    | none => simp [CopyPreconditions.Bodies.statementKindAt,blockAt,stmtAt] at source
    | some statement =>
      have kind : statement.kind = .StorageLive id := by
        simpa [CopyPreconditions.Bodies.statementKindAt,blockAt,stmtAt] using source
      apply SourceSteps.storage_live_exact (PreparedContracts.actualConfig options () remaining span) limits ()
        frames frame machine location block statement id ty located
        (by rw [sourceBody];exact blockAt) stmtAt kind valid (by rw [sourceBody];exact typed)
        _ dead noClocks
      rw [(CanonicalConfigFacts.actual_fields options () remaining span).storage]
      exact trivial

theorem storage_dead
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (location : Location) (id : MIR.LocalId) (value : Immediate Provenance)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (located : frame.location = .mir location)
    (source : CopyPreconditions.Bodies.statementKindAt HelperCompilerFacts.copyBody.body location.block location.statementIndex = some (.StorageDead id))
    (notReturn : id ≠ 0)
    (valid : id < frame.locals.size) (live : frame.locals[id].value = .live (.immediate value)) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () remaining span) limits ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (SourceSteps.deadFrame frame location id valid) machine,.ok true) := by
  cases blockAt : HelperCompilerFacts.copyBody.body.basicBlocks[location.block]? with
  | none => simp [CopyPreconditions.Bodies.statementKindAt,blockAt] at source
  | some block =>
    cases stmtAt : block.statements[location.statementIndex]? with
    | none => simp [CopyPreconditions.Bodies.statementKindAt,blockAt,stmtAt] at source
    | some statement =>
      have kind : statement.kind = .StorageDead id := by
        simpa [CopyPreconditions.Bodies.statementKindAt,blockAt,stmtAt] using source
      exact SourceSteps.storage_dead_exact (PreparedContracts.actualConfig options () remaining span) limits ()
        frames frame machine location block statement id value located
        (by rw [sourceBody];exact blockAt) stmtAt kind valid notReturn live

theorem intrinsic_of_actual_effect
    (config : ExecutionMachine.Config MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
    (limits : ExecutionMachine.Limits)
    (frames : Array CompilerFrameContext.ActualFrame) (frame afterFrame : CompilerFrameContext.ActualFrame)
    (machine afterMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (location : Location) (value : NonDivergingIntrinsic)
    (located : frame.location = .mir location)
    (afterLocated : afterFrame.location = .mir location)
    (source : CopyPreconditions.Bodies.statementKindAt frame.body location.block location.statementIndex = some (.Intrinsic value))
    (actual : (ExecutionMachine.stepHooks config limits).intrinsic () value
      (Storage.withCurrent frames frame machine) = (Storage.withCurrent frames afterFrame afterMachine,.ok ())) :
    ExecutionMachine.step config limits () (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (advance afterFrame location) afterMachine,.ok true) := by
  cases blockAt : frame.body.basicBlocks[location.block]? with
  | none => simp [CopyPreconditions.Bodies.statementKindAt,blockAt] at source
  | some block =>
    cases stmtAt : block.statements[location.statementIndex]? with
    | none => simp [CopyPreconditions.Bodies.statementKindAt,blockAt,stmtAt] at source
    | some statement =>
      have kind : statement.kind = .Intrinsic value := by
        simpa [CopyPreconditions.Bodies.statementKindAt,blockAt,stmtAt] using source
      have effect : Step.evalStatement (ExecutionMachine.stepHooks config limits) () statement
          (Storage.withCurrent frames frame machine) =
          (Storage.withCurrent frames afterFrame afterMachine,.ok ()) := by
        unfold Step.evalStatement
        simpa only [kind] using actual
      have result := StepFacts.step_statement (ExecutionMachine.stepHooks config limits) ()
        (Storage.withCurrent frames frame machine) (Storage.withCurrent frames afterFrame afterMachine)
        frame afterFrame location location block statement
        (by simp [Storage.withCurrent,Stack.currentFrame?]) located blockAt stmtAt effect
        (by simp [Storage.withCurrent]) (by simp [Storage.withCurrent,Stack.currentFrame?]) afterLocated
        (by simp [Storage.withCurrent])
      simpa [ExecutionMachine.step,Storage.withCurrent,advance,Array.set_push] using result


#print axioms assign_of_actual_rvalue
open Lean Elab Command in
run_cmd do
  for declaration in [``assign_of_actual_rvalue, ``source_copy_step, ``destination_copy_step, ``count_copy_step, ``unit_assignment_step, ``storage_live, ``storage_dead, ``intrinsic_of_actual_effect] do
   for dependency in (← collectAxioms declaration) do
     unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
       throwError "unapproved axiom {dependency}"
end DuplicatePrefix.CopyHelperSteps
