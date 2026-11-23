import Miri.Verification.ExactWP
import Init.Internal.Order.While

/-! Verify the canonical driver selects the symbolic assignment continuation
and routes its remaining effect to the actual typed copy. -/
namespace MiriTests.Verification.RvalueWP

open Miri.ABI Miri.DataStructures Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Verification
open Miri.TreeBorrows.RetagPolicy Std.WP

set_option experimental.vcgen true

variable {K U O X Host : Type} [DecidableEq K]
local notation "State" => MachineHooks.State K U
local notation "Config" => ExecutionMachine.Config K U Unit O X Host
local notation "Frame" => Miri.Interpreter.Frame Provenance LocalLayout MachineHooks.FrameExtra

theorem use_vcgen (config : Config) (limits : ExecutionMachine.Limits)
    (place : Place) (rhs : Operand) (before projected copying : State)
    (frame : Frame) (loc : Location) (block : BasicBlock) (stmt : Statement)
    (destination : RuntimePlace Provenance) (source : OpTy Provenance)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (statement : block.statements[loc.statementIndex]? = some stmt)
    (kind : stmt.kind = .Assign place (.Use rhs .No))
    (placeOk : PlaceDynamic.evalPlace (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits))
      () place true before = .ok destination projected)
    (operandOk : OperandMachine.evalOperand (ExecutionMachine.operandHooks
      (ExecutionMachine.withValidation (ExecutionMachine.withValidation config limits) limits))
      () rhs (some destination.layout) projected = .ok source copying)
    (copyChecked : RvalueWP.retagModePre .None
      (copyRuntimePlace (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place
        (ExecutionMachine.withValidation (ExecutionMachine.withValidation config limits) limits).copy () source destination false)
      (fun _ => InstructionWP.finishStatementResultPre
        (before.stack.frames.size - 1) (fun actual after => actual = true ∧ post () after)
        onError) onError copying) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simp only [miri_rvalue, current, position, selected, statement, kind]
  have prepared : PlaceDynamic.evalPlace
      (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation (ExecutionMachine.withValidation config limits) limits))
      () place true before = .ok destination projected := placeOk
  rw [RvalueWP.actionPre_ok prepared, RvalueWP.actionPre_ok operandOk]
  exact copyChecked

/-- A padded, indirect source follows the physical copy path. Its arbitrary
success and error continuations are passed to the production typed copy. -/
theorem indirect_copy (config : Config) (limits : ExecutionMachine.Limits)
    (destination : RuntimePlace Provenance) (source : OpTy Provenance)
    (memorySource : MemPlace Provenance) (memoryDest : MPlaceTy Provenance)
    (before allocated : State) (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (compatible : (ExecutionMachine.withValidation config limits).copy.compatible
      source.layout destination.layout = .ok true)
    (padding : (ExecutionMachine.withValidation config limits).copy.hasPadding source.layout = .ok true)
    (sourceMemory : source.op = .indirect memorySource)
    (destMemory : forceAllocation (ExecutionMachine.projectionHooks config).place () destination
      before = .ok memoryDest allocated) :
    RvalueWP.actionPre
      (copyRuntimePlaceNoValidate (ExecutionMachine.projectionHooks config).place
        (ExecutionMachine.withValidation config limits).copy () source destination false)
      post onError before =
      wp (GlobalMemoryCopyMachine.typedCopy config.access config.addresses config.arithmetic
        config.projection.dynamic config.projection.dynamicFuel config.compiler.debugAssertions
        () ⟨memorySource, source.layout⟩ memoryDest) post onError allocated := by
  simp only [copyRuntimePlaceNoValidate, compatible, padding, placeLift_ok,
    RvalueWP.actionPre_bind, RvalueWP.actionPre_pure, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    sourceMemory]
  rw [RvalueWP.actionPre_ok destMemory, RvalueWP.canonical_memoryCopy, RvalueWP.actionPre_eq_wp]

section AliasedRead

attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

private def aliasTag : BorTag := ⟨2, by decide⟩
private def oneByte := Size.ofBytes 1

private def disabledChild : BorrowTree :=
  let root := BorrowTree.new BorTag.one oneByte
  let permissions := DedupRangeMap.new oneByte (⟨.Frozen, true, .Read⟩ : Tree.LocationState)
  let inserted := root.newChild Size.ZERO (.concrete BorTag.one) aliasTag permissions .Frozen true
  (inserted.tree.performBorrowAccessRange (.concrete BorTag.one)
    Size.ZERO oneByte .Write {} .VisitChildrenOfAccessed).tree

private def failedRead := disabledChild.performBorrowAccessRange (.concrete aliasTag)
  Size.ZERO oneByte .Read {} .VisitChildrenOfAccessed

set_option maxRecDepth 65536 in
set_option cbv.maxSteps 1000000 in
private theorem failedReadStatus :
    failedRead.status =
      .AccessFailure ⟨0, 1⟩ (.TransitionError 1 (.ChildAccessForbidden .Disabled)) := by
  cbv

/-- An earlier parent write disabled the alias used by the MIR operand.
The read fails before the unary operation or destination write. The error
continuation sees the actual failure and the state committed by the access. -/
theorem aliased_read (config : Config) (limits : ExecutionMachine.Limits)
    (place : Place) (operand : Operand) (before projected reading : State)
    (frame : Frame) (loc : Location) (block : BasicBlock) (stmt : Statement)
    (destination : RuntimePlace Provenance) (source : OpTy Provenance) (mplace : MemPlace Provenance)
    (primitive : BackendPrimitive) (validRange : WrappingRange)
    (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (current : before.stack.currentFrame? = some frame)
    (position : frame.location = .mir loc)
    (selected : frame.body.basicBlocks[loc.block]? = some block)
    (statement : block.statements[loc.statementIndex]? = some stmt)
    (kind : stmt.kind = .Assign place (.UnaryOp .Not operand))
    (placeOk : PlaceDynamic.evalPlace (ExecutionMachine.projectionHooks config)
      () place true before = .ok destination projected)
    (operandOk : OperandMachine.evalOperand (ExecutionMachine.operandHooks
      (ExecutionMachine.withValidation (ExecutionMachine.withValidation config limits) limits))
      () operand (some destination.layout) projected = .ok source reading)
    (indirect : source.op = .indirect mplace)
    (backend : (localMemoryLayout source.layout).backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := validRange)))
    (width : primitive.size config.access.runtime = .ok (localMemoryLayout source.layout).size)
    (checked : MemoryWP.CheckedPlaceAccess config.access false reading.machine.memory
      ⟨reading.machine, none⟩ ⟨mplace, localMemoryLayout source.layout⟩)
    (alias : checked.resolved.extra = .concrete aliasTag)
    (tree : checked.allocation.extra = disabledChild)
    (offset : checked.resolved.offset = Size.ZERO)
    (size : (localMemoryLayout source.layout).size = oneByte)
    (diagnosed raced : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (diagnostic : config.access.diagnostic false checked.resolved.allocId
      (allocRange Size.ZERO oneByte) checked.accessHooks.machine = .ok () diagnosed)
    (race : MachineHooks.memoryRaceAccess diagnosed checked.resolved.allocId
      (allocRange Size.ZERO oneByte) none .Read = (raced, .ok ()))
    (tracked : raced.borrowTracker = some tracker)
    (unprotected : tracker.global.protectedTags = {})
    (acceptError :
      let error := PlaceMachine.treeError false failedRead.status
      let ref : AllocationAccessRef Provenance BorrowTree :=
        ⟨checked.resolved.allocId, allocRange Size.ZERO oneByte, checked.allocation⟩
      let hook : AllocationExtraHookResult (PlaceMachine.AccessState K U) BorrowTree :=
        ⟨⟨raced, some error⟩, failedRead.tree, .error (reprStr error)⟩
      let result := AllocationAccess.finishCheckedAccess false checked.rawMemory ref hook
      onError error {reading with machine :=
        config.access.retainTouched {raced with memory := result.memory} result.touched}) :
    Triple (StepWP.Program.step (hooks := ExecutionMachine.stepHooks config limits)
        (allowed := fun _ _ => True) true)
      (· = before) post onError := by
  have readChecked (afterRead : RvalueImmTy Provenance → State → Prop) :
      wp (PlaceMachine.readImmediate config.access source) afterRead onError reading := by
    rw [MemoryWP.readImmediate_iff,
      MemoryWP.scalarRead_resultPre_iff config.access source mplace primitive validRange
        afterRead onError reading checked indirect backend width]
    simp only [MemoryWP.CheckedPlaceAccess.pre, MemoryWP.memoryAccessPre, MemoryWP.policyPre,
      wp, WP.wpTrans, offset, size, diagnostic, race, Bool.false_eq_true, ↓reduceIte, tracked,
      tree, alias, unprotected, TreeBorrowsWP.accessPre_iff]
    simp only [allocRange]
    rw [← failedRead]
    simp only [failedReadStatus, MemoryWP.failurePre]
    -- A Tree Borrows error reaches the caller even if caching the tree failed.
    simp only [MemoryWP.resultPre, scalarReadAfterAccess, finishPlaceAccess,
      AllocationAccess.finishCheckedAccess, failedReadStatus] at acceptError ⊢
    generalize (if checked.rawMemory.live.any (fun row => row.1 == checked.resolved.allocId) then
      checked.rawMemory.setLiveAllocation checked.resolved.allocId
        (checked.allocation.setExtra failedRead.tree)
      else .ok checked.rawMemory) = cached at acceptError ⊢
    cases cached <;> exact acceptError
  vcgen
  rename_i state equal
  subst state
  refine ⟨⟨(), trivial⟩, ?_⟩
  rintro ⟨⟩ _
  simp only [miri_rvalue, current, position, selected, statement, kind]
  have projectedOk : PlaceDynamic.evalPlace
      (ExecutionMachine.projectionHooks
        (ExecutionMachine.withValidation (ExecutionMachine.withValidation config limits) limits))
      () place true before = .ok destination projected := placeOk
  rw [RvalueWP.actionPre_ok projectedOk]
  simp only [UnOp.homogeneous, ↓reduceIte]
  rw [RvalueWP.actionPre_ok operandOk]
  change RvalueWP.actionPre (PlaceMachine.readImmediate config.access source) _ onError reading
  rw [RvalueWP.actionPre_eq_wp]
  exact readChecked _

end AliasedRead

end MiriTests.Verification.RvalueWP
