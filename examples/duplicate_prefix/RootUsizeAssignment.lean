import duplicate_prefix.PointerAddStatements
namespace DuplicatePrefix.RootUsizeAssignment
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
inductive Kind where
  | guardCount | addCount | copyCount

def destId : Kind → Miri.MIR.LocalId
  | .guardCount => 9 | .addCount => 23 | .copyCount => 24

def siteLocation : Kind → Location
  | .guardCount => ⟨2,7⟩ | .addCount => ⟨7,12⟩ | .copyCount => ⟨8,3⟩

theorem normalized_dest (kind : Kind) (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame (destId kind) = .ok 5 := by
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
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (count : UInt64) (kind : Kind)
    (validSource : (2 : Miri.MIR.LocalId) < frame.locals.size)
    (validDest : (destId kind : Miri.MIR.LocalId) < frame.locals.size)
    (sourceLive : frame.locals[2].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (sourceCached : frame.locals[2].layout = some RootCompilerFacts.usizeLayout)
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
        {(ActualLocalCopy.written frame (destId kind) RootCompilerFacts.usizeLayout validDest (.scalar (.fromScalarInt (.ofUInt64 count)))) with location := .mir {(siteLocation kind) with statementIndex := (siteLocation kind).statementIndex+1}}
        machine, .ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let block := sourceBlock kind
  let statement := sourceStatement kind
  have blockAt : frame.body.basicBlocks[(siteLocation kind).block]? = some block := by rw [sourceBody];cases kind <;> with_unfolding_all rfl
  have statementAt : block.statements[(siteLocation kind).statementIndex]? = some statement := by cases kind <;> with_unfolding_all rfl
  have stmtKind : statement.kind = .Assign ⟨destId kind,#[]⟩ (.Use (.Copy ⟨2,#[]⟩) .Yes) := by cases kind <;> with_unfolding_all rfl
  have normalized := normalized_dest kind frame sourceBody identity callee
  have lookup : PreparedReflection.actual.compiler.runtime.lookup 5 = .ok RootCompilerFacts.usizeLayout := by
    with_unfolding_all exact RootCompilerFacts.usize_layout_eq
  have query := PointerAddFacts.compute_local framesBefore frame machine (destId kind) 5 RootCompilerFacts.usizeLayout normalized lookup
  have effect := ScalarLocalCopy.usize options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine 2 (destId kind) count (by cases kind <;> decide) validSource validDest sourceLive sourceCached
    destLive destUncached query noClocks tracker tracked defaultMode ghostFalse shallow
  have afterLocation : (ActualLocalCopy.written frame (destId kind) RootCompilerFacts.usizeLayout validDest (.scalar (.fromScalarInt (.ofUInt64 count)))).location = .mir (siteLocation kind) := by
    simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,located]
  exact SourceSteps.assign_exact config limits () framesBefore frame _ machine machine (siteLocation kind) block statement
    ⟨destId kind,#[]⟩ (.Use (.Copy ⟨2,#[]⟩) .Yes) located blockAt statementAt stmtKind effect afterLocation

#print axioms step
end DuplicatePrefix.RootUsizeAssignment
