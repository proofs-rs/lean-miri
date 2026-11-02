import duplicate_prefix.LiteralUse
import duplicate_prefix.LiteralConstant
import duplicate_prefix.CopyHelperUnit
import duplicate_prefix.PointerAddFacts
import duplicate_prefix.SourceSteps
namespace DuplicatePrefix.RootUnitAssignment
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

inductive Kind where
  | initial | afterGuard | afterCopy

def localIdOf : Kind → Miri.MIR.LocalId
  | .initial => 3 | .afterGuard => 7 | .afterCopy => 17

def location : Kind → Location
  | .initial => ⟨2,1⟩ | .afterGuard => ⟨6,2⟩ | .afterCopy => ⟨9,4⟩

def sourceSpan : Kind → SpanRef
  | .initial => ⟨7⟩ | .afterGuard => ⟨20⟩ | .afterCopy => ⟨27⟩

noncomputable def site (kind : Kind) : CompilerConstantQueries.Site :=
  ⟨RootBody.reflected.body.identity.index,location kind,
    #[.field "kind",.field "rvalue",.field "operand",.field "constant"]⟩

def constant (kind : Kind) : ConstOperand := ⟨sourceSpan kind,none,.Val .ZeroSized 2⟩

theorem normalization (kind : Kind) : normalizationFromEvidence (LiteralConstant.evidence (site kind))
    RootBody.reflected.functionInstance (.Val .ZeroSized 2) = .ok (.Val .ZeroSized 2) := by
  cases kind <;> with_unfolding_all rfl

theorem conversion (queries : ConstantValueQueries Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (ConstantMachine.Context MiriMemoryKind Machine.RootUser))
    (state : ConstantState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (ConstantMachine.Context MiriMemoryKind Machine.RootUser)) :
    valueToOpWithLayout PreparedReflection.actual.compiler.runtime queries .ZeroSized 2
      (some CopyHelperUnit.layout) none state =
    .ok ⟨.immediate .uninit,CopyHelperUnit.layout⟩ state := by
  with_unfolding_all rfl

theorem normalized_local (kind : Kind) (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame (localIdOf kind) = .ok 2 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [body,identity,callee]
  cases kind <;> with_unfolding_all rfl

theorem evaluate
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1) (kind : Kind)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : localIdOf kind < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localIdOf kind].value = .live (.immediate old))
    (uncached : frame.locals[localIdOf kind].layout = none)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (location kind))
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Use (.Constant (constant kind)) .Yes) ⟨localIdOf kind,#[]⟩
      (Storage.withCurrent framesBefore frame machine) =
    .ok () (Storage.withCurrent framesBefore
      (ActualLocalCopy.written frame (localIdOf kind) CopyHelperUnit.layout valid .uninit) machine) := by
  let cached := LocalPlaces.cachePlaceLayout frame (localIdOf kind) CopyHelperUnit.layout valid
  have lookup : PreparedReflection.actual.compiler.runtime.lookup 2 = .ok CopyHelperUnit.layout := by
    with_unfolding_all exact CopyHelperUnit.layout_query
  have query := PointerAddFacts.compute_local framesBefore frame machine (localIdOf kind) 2 CopyHelperUnit.layout
    (normalized_local kind frame body identity callee) lookup
  have operand := LiteralConstant.operand_at options limits (remaining+1) span source debugOff
    (site kind) (OperandPath.rvalue "operand") (by simp [site,OperandPath.rvalue])
    .ZeroSized 2 (sourceSpan kind) (some CopyHelperUnit.layout) .uninit CopyHelperUnit.layout
    (normalization kind) conversion framesBefore cached machine
    (congrArg (fun id : BodyIdentity => id.index) identity) located callee
  have v : localIdOf kind < cached.locals.size := by simpa [cached,LocalPlaces.cachePlaceLayout] using valid
  have oldLive : cached.locals[localIdOf kind].value = .live (.immediate old) := by
    simpa [cached,LocalPlaces.cachePlaceLayout] using live
  have cache : cached.locals[localIdOf kind].layout = some CopyHelperUnit.layout := by simp [cached,LocalPlaces.cachePlaceLayout]
  have copied := CopyHelperUnit.copy_unit_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore cached machine (localIdOf kind) old v oldLive cache noClocks ghostFalse shallow
  exact LiteralUse.uncached options limits remaining span debugOff framesBefore frame machine
    (constant kind) (localIdOf kind) CopyHelperUnit.layout .uninit CopyHelperUnit.layout_shape.2.1 valid uncached
    query tracker tracked defaultMode operand copied

theorem block_bound (kind : Kind) : (location kind).block < RootBody.reflected.body.body.basicBlocks.size := by
  cases kind <;> with_unfolding_all decide +kernel

noncomputable def sourceBlock (kind : Kind) := RootBody.reflected.body.body.basicBlocks[(location kind).block]'(block_bound kind)

theorem statement_bound (kind : Kind) : (location kind).statementIndex < (sourceBlock kind).statements.size := by
  cases kind <;> with_unfolding_all decide +kernel

noncomputable def sourceStatement (kind : Kind) := (sourceBlock kind).statements[(location kind).statementIndex]'(statement_bound kind)

theorem step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1) (kind : Kind)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : localIdOf kind < frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localIdOf kind].value = .live (.immediate old))
    (uncached : frame.locals[localIdOf kind].layout = none)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (location kind))
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore
        {(ActualLocalCopy.written frame (localIdOf kind) CopyHelperUnit.layout valid .uninit) with
          location := .mir {(location kind) with statementIndex := (location kind).statementIndex+1}}
        machine,.ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let loc := location kind
  let block := sourceBlock kind
  let statement := sourceStatement kind
  have blockAt : frame.body.basicBlocks[loc.block]? = some block := by rw [body];cases kind <;> with_unfolding_all rfl
  have statementAt : block.statements[loc.statementIndex]? = some statement := by cases kind <;> with_unfolding_all rfl
  have stmtKind : statement.kind = .Assign ⟨localIdOf kind,#[]⟩ (.Use (.Constant (constant kind)) .Yes) := by
    cases kind <;> with_unfolding_all rfl
  have effect := evaluate options limits remaining span source debugOff fuel validationFuel kind
    framesBefore frame machine valid old live uncached body identity callee located noClocks tracker tracked defaultMode ghostFalse shallow
  have afterLocation : (ActualLocalCopy.written frame (localIdOf kind) CopyHelperUnit.layout valid .uninit).location = .mir loc := by
    simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,located,loc]
  exact SourceSteps.assign_exact config limits () framesBefore frame _ machine machine loc block statement
    ⟨localIdOf kind,#[]⟩ (.Use (.Constant (constant kind)) .Yes) located blockAt statementAt stmtKind effect afterLocation

#print axioms step

#print axioms evaluate
end DuplicatePrefix.RootUnitAssignment
