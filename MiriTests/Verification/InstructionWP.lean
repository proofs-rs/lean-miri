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

end MiriTests.Verification.InstructionWP
