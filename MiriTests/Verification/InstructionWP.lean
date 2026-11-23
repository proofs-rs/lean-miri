import Miri.Verification.ExactWP

/-! The canonical driver exposes storage cleanup and discriminant assignment
through their production effects with arbitrary error continuations. -/
namespace MiriTests.Verification.InstructionWP

open Miri.Interpreter Miri.Memory Miri.MIR Miri.Verification Std.WP

set_option experimental.vcgen true

variable {K U O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U Unit O X Host
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra

/-- The deallocation runs after the local has become dead. Its error
continuation is the caller's original error continuation. -/
example (config : Config) (limits : ExecutionMachine.Limits)
    (before : State) (frame updated : Frame) (loc : Location)
    (block : BasicBlock) (stmt : Statement) (id : LocalId)
    (old : LocalState Provenance LocalLayout) (place : MemPlace Provenance)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (statement : block.statements[loc.statementIndex]? = some stmt) (kind : stmt.kind = .StorageDead id)
    (nonReturn : ¬(id == 0) = true) (nonempty : ¬before.stack.frames.isEmpty = true)
    (slot : frame.getLocal id = .ok old) (owned : old.value = .live (.indirect place))
    (dead : frame.replaceLocalValue id .dead = .ok updated)
    (deallocate : wp ((ExecutionMachine.withValidation config limits).lifecycle.storage.deallocateStack
      place.ptr) (fun _ => InstructionWP.finishStatementResultPre
        (before.stack.frames.size - 1) (fun actual after => actual = true ∧ post () after) onError)
      onError { before with stack := ⟨before.stack.frames.pop.push updated⟩ }) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simp only [miri_rvalue, current, position, selected, statement, kind,
    CanonicalStepWP.storageDeadPre, nonReturn, nonempty, slot, owned, dead]
  exact deallocate

/-- A failed projection prevents the discriminant write. The caller checks
the actual post-projection state. -/
example (config : Config) (limits : ExecutionMachine.Limits)
    (before failed : State) (frame : Frame) (loc : Location)
    (block : BasicBlock) (stmt : Statement) (place : Place) (variant : VariantIndex)
    (error : StepError) (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (statement : block.statements[loc.statementIndex]? = some stmt)
    (kind : stmt.kind = .SetDiscriminant place variant)
    (projected : PlaceDynamic.evalPlace
      (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits))
      () place false before = .error error failed)
    (acceptError : onError error failed) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simpa only [miri_rvalue, current, position, selected, statement, kind,
    wp, WP.wpTrans, projected] using acceptError

/-- The copy intrinsic evaluates its three operands in source order before
entering the canonical memory copy path. -/
example (config : Config) (limits : ExecutionMachine.Limits)
    (args : CopyNonOverlapping) (before sourceRead destinationRead countRead : State)
    (frame : Frame) (loc : Location) (block : BasicBlock) (stmt : Statement)
    (source dest count : OpTy Provenance)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (statement : block.statements[loc.statementIndex]? = some stmt)
    (kind : stmt.kind = .Intrinsic (.CopyNonOverlapping args))
    (evalSource : OperandMachine.evalOperand
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits))
      () args.source none before = .ok source sourceRead)
    (evalDestination : OperandMachine.evalOperand
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits))
      () args.destination none sourceRead = .ok dest destinationRead)
    (evalCount : OperandMachine.evalOperand
      (ExecutionMachine.operandHooks (ExecutionMachine.withValidation config limits))
      () args.count none destinationRead = .ok count countRead)
    (copy : wp (Intrinsics.copyWith
      (ExecutionMachine.memoryIntrinsicHooks (ExecutionMachine.withValidation config limits))
      () source dest count true) (fun _ => InstructionWP.finishStatementResultPre
        (before.stack.frames.size - 1) (fun actual after => actual = true ∧ post () after) onError)
      onError countRead) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simp only [miri_rvalue, current, position, selected, statement, kind]
  simp only [Intrinsics.evalNondivergingWith, wp, WP.wpTrans, bind, Bind.bind, EStateM.bind,
    evalSource, evalDestination, evalCount]
  exact copy

private abbrev validated (config : Config) (limits : ExecutionMachine.Limits) :=
  ExecutionMachine.withValidation config limits

private abbrev callDictionary (config : Config) (limits : ExecutionMachine.Limits) :=
  ExecutionMachine.callHooks (validated config limits) limits

/-- A callee operand error after evaluating the destination takes the failure
continuation before argument evaluation or call dispatch. -/
example (config : Config) (limits : ExecutionMachine.Limits)
    (before ready indexed framed projected failed : State) (frame observed : Frame) (loc : Location)
    (block : BasicBlock) (term : Terminator) (func : Miri.MIR.Operand)
    (args : Array SpannedOperand) (dest : Place) (target : Option BasicBlockId)
    (unwind : UnwindAction) (source : CallSource) (span : SpanRef)
    (destination : RuntimeStackPlace Provenance) (index : Nat) (error : StepError)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (noStatement : block.statements[loc.statementIndex]? = none) (terminator : block.terminator = term)
    (kind : term.kind = .Call func args dest target unwind source span)
    (prepared : TerminatorMachine.beforeTerminatorWithChoice (validated config limits).terminators
      ((validated config limits).preemptionChoice ()) before = .ok () ready)
    (indexedOk : (callDictionary config limits).frameIndex ready = .ok index indexed)
    (frameOk : (callDictionary config limits).getFrame indexed = .ok observed framed)
    (projectedOk : (callDictionary config limits).evalPlace () dest false framed =
      .ok destination projected)
    (calleeError : (callDictionary config limits).evalOperand () func projected = .error error failed)
    (acceptError : onError error failed) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simp only [miri_rvalue, current, position, selected, noStatement, terminator,
    CanonicalStepWP.terminatorPre, wp, WP.wpTrans, prepared]
  simp only [CanonicalStepWP.selectedTerminatorPre, kind, wp, WP.wpTrans,
    Call.evalCallTerminator, Call.evalCalleeAndArgs, bind, Bind.bind, EStateM.bind,
    indexedOk, frameOk, projectedOk, calleeError]
  exact acceptError

/-- Optional overflow checks still evaluate the assertion operand before
testing the value or dispatching a panic. -/
example (config : Config) (limits : ExecutionMachine.Limits)
    (before ready failed : State) (frame : Frame) (loc : Location)
    (block : BasicBlock) (term : Terminator) (condition : Miri.MIR.Operand)
    (expected : Bool) (message : AssertKind) (target : BasicBlockId) (unwind : UnwindAction)
    (error : StepError) (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (noStatement : block.statements[loc.statementIndex]? = none) (terminator : block.terminator = term)
    (kind : term.kind = .Assert condition expected message target unwind)
    (prepared : TerminatorMachine.beforeTerminatorWithChoice (validated config limits).terminators
      ((validated config limits).preemptionChoice ()) before = .ok () ready)
    (operandError : OperandMachine.evalOperand (ExecutionMachine.operandHooks (validated config limits))
      () condition none ready = .error error failed)
    (acceptError : onError error failed) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simp only [miri_rvalue, current, position, selected, noStatement, terminator,
    CanonicalStepWP.terminatorPre, wp, WP.wpTrans, prepared]
  simp only [CanonicalStepWP.selectedTerminatorPre, kind, CanonicalStepWP.assertConditionEffect,
    wp, WP.wpTrans, bind, Bind.bind, EStateM.bind, operandError]
  exact acceptError

/-- Async drop is rejected before evaluating the place. The rejection uses
the state returned by the pre-terminator action. -/
example (config : Config) (limits : ExecutionMachine.Limits)
    (before ready : State) (frame : Frame) (loc : Location)
    (block : BasicBlock) (term : Terminator) (place : Place) (target resume : BasicBlockId)
    (unwind : UnwindAction) (replace : Bool)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (noStatement : block.statements[loc.statementIndex]? = none) (terminator : block.terminator = term)
    (kind : term.kind = .Drop place target unwind replace (some resume))
    (prepared : TerminatorMachine.beforeTerminatorWithChoice (validated config limits).terminators
      ((validated config limits).preemptionChoice ()) before = .ok () ready)
    (acceptError : onError (.invalidProgram "Async Drop must be expanded or reset to sync") ready) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simpa only [miri_rvalue, current, position, selected, noStatement, terminator, kind,
    CanonicalStepWP.terminatorPre, CanonicalStepWP.selectedTerminatorPre, wp, WP.wpTrans, prepared,
    Option.isSome_some, ↓reduceIte] using acceptError

/-- Tail calls evaluate the callee in the state after reading the original
frame index. Operand failure takes precedence over the tail-call checks. -/
example (config : Config) (limits : ExecutionMachine.Limits)
    (before ready indexed failed : State) (frame : Frame) (loc : Location)
    (block : BasicBlock) (term : Terminator) (func : Miri.MIR.Operand) (args : Array SpannedOperand)
    (span : SpanRef) (index : Nat) (error : StepError)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (noStatement : block.statements[loc.statementIndex]? = none) (terminator : block.terminator = term)
    (kind : term.kind = .TailCall func args span)
    (prepared : TerminatorMachine.beforeTerminatorWithChoice (validated config limits).terminators
      ((validated config limits).preemptionChoice ()) before = .ok () ready)
    (indexedOk : (callDictionary config limits).frameIndex ready = .ok index indexed)
    (calleeError : (callDictionary config limits).evalOperand () func indexed = .error error failed)
    (acceptError : onError error failed) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simp only [miri_rvalue, current, position, selected, noStatement, terminator,
    CanonicalStepWP.terminatorPre, wp, WP.wpTrans, prepared]
  simp only [CanonicalStepWP.selectedTerminatorPre, kind, wp, WP.wpTrans,
    Call.evalTailCallTerminator, Call.evalCalleeAndArgs, bind, Bind.bind, EStateM.bind,
    indexedOk, calleeError]
  exact acceptError

end MiriTests.Verification.InstructionWP
