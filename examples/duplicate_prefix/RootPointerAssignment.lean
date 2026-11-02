import duplicate_prefix.PointerAddStatements
namespace DuplicatePrefix.RootPointerAssignment
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
inductive Kind where
  | castInput | addInput

def destId : Kind → Miri.MIR.LocalId
  | .castInput => 20 | .addInput => 22

def siteLocation : Kind → Location
  | .castInput => ⟨7,5⟩ | .addInput => ⟨7,10⟩

theorem normalized_dest (kind : Kind) (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame (destId kind) = .ok 8 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [body,identity,callee]
  cases kind <;> with_unfolding_all rfl

theorem block_bound (kind : Kind) : (siteLocation kind).block < RootBody.reflected.body.body.basicBlocks.size := by
  cases kind <;> with_unfolding_all decide +kernel

noncomputable def sourceBlock (kind : Kind) := RootBody.reflected.body.body.basicBlocks[(siteLocation kind).block]'(block_bound kind)

theorem statement_bound (kind : Kind) : (siteLocation kind).statementIndex < (sourceBlock kind).statements.size := by
  cases kind <;> with_unfolding_all decide +kernel

noncomputable def sourceStatement (kind : Kind) := (sourceBlock kind).statements[(siteLocation kind).statementIndex]'(statement_bound kind)

theorem step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (value : Scalar Provenance) (kind : Kind)
    (validSource : (15 : Miri.MIR.LocalId) < frame.locals.size)
    (validDest : (destId kind : Miri.MIR.LocalId) < frame.locals.size)
    (sourceLive : frame.locals[15].value = .live (.immediate (.scalar value)))
    (sourceCached : frame.locals[15].layout = some CopyCompilerFacts.destPointerLayout)
    (destLive : frame.locals[destId kind].value = .live (.immediate .uninit))
    (destUncached : frame.locals[destId kind].layout = none)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (siteLocation kind))
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore
        {(ActualLocalCopy.written frame (destId kind) CopyCompilerFacts.destPointerLayout validDest (.scalar value)) with location := .mir {(siteLocation kind) with statementIndex := (siteLocation kind).statementIndex+1}}
        machine, .ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := sourceBlock kind
  let statement := sourceStatement kind
  have blockAt : frame.body.basicBlocks[(siteLocation kind).block]? = some block := by rw [sourceBody];cases kind <;> with_unfolding_all rfl
  have statementAt : block.statements[(siteLocation kind).statementIndex]? = some statement := by cases kind <;> with_unfolding_all rfl
  have stmtKind : statement.kind = .Assign ⟨destId kind,#[]⟩ (.Use (.Copy ⟨15,#[]⟩) .Yes) := by cases kind <;> with_unfolding_all rfl
  have normalized := normalized_dest kind frame sourceBody identity callee
  have lookup : PreparedReflection.actual.compiler.runtime.lookup 8 = .ok CopyCompilerFacts.destPointerLayout := by
    with_unfolding_all exact CopyCompilerFacts.dest_pointer_layout_eq
  have query := PointerAddFacts.compute_local framesBefore frame machine (destId kind) 8 CopyCompilerFacts.destPointerLayout normalized lookup
  have effect := ScalarLocalCopy.pointer options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine 15 (destId kind) value (by cases kind <;> decide) validSource validDest sourceLive sourceCached
    destLive destUncached query noClocks tracker tracked defaultMode ghostFalse shallow
  have afterLocation : (ActualLocalCopy.written frame (destId kind) CopyCompilerFacts.destPointerLayout validDest (.scalar value)).location = .mir (siteLocation kind) := by
    simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,located]
  exact SourceSteps.assign_exact config limits () framesBefore frame _ machine machine (siteLocation kind) block statement
    ⟨destId kind,#[]⟩ (.Use (.Copy ⟨15,#[]⟩) .Yes) located blockAt statementAt stmtKind effect afterLocation

#print axioms step
end DuplicatePrefix.RootPointerAssignment
