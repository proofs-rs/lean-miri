import duplicate_prefix.Program
import Miri.Input.CallResolution
import Miri.Input.LowerMIR
import Miri.Interpreter.Stack
import Lean.Elab.Deriving.ToExpr
import duplicate_prefix.FrameFacts

/-! A build-time reflection of production lowering and compiler call-resolution
output. Like `import_mir`, the generator/import chain is an input trust
boundary; kernel facts below concern the reflected closed values. The entry
frame constructor stores ABI-shaped arguments but deliberately does not run
`initFnCall`, FnEntry retagging, validity checks, stack lifecycle hooks, or
validate the buffer allocation. It is an entry-frame shape only.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open Lean Miri Miri.ABI Miri.Input Miri.Interpreter Miri.MIR Miri.Memory

-- Local expression quoters for the fixed MIR AST. These are used only to
-- reflect values produced by the pinned production lowerer during elaboration.
deriving instance ToExpr for MIR.BinOp
deriving instance ToExpr for MIR.UnOp
deriving instance ToExpr for MIR.Location
deriving instance ToExpr for MIR.SpanRef
deriving instance ToExpr for MIR.Mutability
deriving instance ToExpr for MIR.Safety
deriving instance ToExpr for MIR.Variance
deriving instance ToExpr for MIR.PointerCoercion
deriving instance ToExpr for MIR.CoercionSource
deriving instance ToExpr for MIR.CastKind
deriving instance ToExpr for MIR.FakeBorrowKind
deriving instance ToExpr for MIR.MutBorrowKind
deriving instance ToExpr for MIR.BorrowKind
deriving instance ToExpr for MIR.RawPtrKind
deriving instance ToExpr for MIR.WithRetag
deriving instance ToExpr for MIR.RuntimeChecks
deriving instance ToExpr for MIR.LoopHintAttr
deriving instance ToExpr for MIR.FakeReadCause
deriving instance ToExpr for MIR.CallSource
deriving instance ToExpr for MIR.InlineAsmMacro
deriving instance ToExpr for MIR.UnwindTerminateReason
deriving instance ToExpr for MIR.UnwindAction
deriving instance ToExpr for MIR.CoroutineSource
deriving instance ToExpr for MIR.CoroutineDesugaring
deriving instance ToExpr for MIR.Movability
deriving instance ToExpr for MIR.CoroutineKind
deriving instance ToExpr for MIR.HirId
deriving instance ToExpr for MIR.CoveragePointKind
deriving instance ToExpr for MIR.CoverageKind
deriving instance ToExpr for MIR.BackwardIncompatibleDropReason
deriving instance ToExpr for MIR.ProjectionKind
deriving instance ToExpr for MIR.UserTypeProjection
deriving instance ToExpr for MIR.AnalysisPhase
deriving instance ToExpr for MIR.RuntimePhase
deriving instance ToExpr for MIR.MirPhase
deriving instance ToExpr for MIR.ConstPointer
deriving instance ToExpr for MIR.ScalarValue
deriving instance ToExpr for MIR.ConstValue
deriving instance ToExpr for MIR.ConstAliasKind
deriving instance ToExpr for MIR.ConstExpressionCastKind
deriving instance ToExpr for MIR.ConstExpressionKind
deriving instance ToExpr for MIR.BoundVarIndexKind
deriving instance ToExpr for MIR.BoundRegionKind
deriving instance ToExpr for MIR.BoundTypeKind
deriving instance ToExpr for MIR.BoundVariableKind
deriving instance ToExpr for MIR.LateParamRegionKind
deriving instance ToExpr for MIR.Region
deriving instance ToExpr for MIR.GenericArg
deriving instance ToExpr for MIR.ValTreeNode
deriving instance ToExpr for MIR.ValTree
deriving instance ToExpr for MIR.TypeConst
deriving instance ToExpr for MIR.UnevaluatedConst
deriving instance ToExpr for MIR.MirConst
deriving instance ToExpr for MIR.ConstOperand
deriving instance ToExpr for MIR.ProjectionElem
deriving instance ToExpr for MIR.Place
deriving instance ToExpr for MIR.Operand
deriving instance ToExpr for MIR.CopyNonOverlapping
deriving instance ToExpr for MIR.NonDivergingIntrinsic
deriving instance ToExpr for MIR.AggregateKind
deriving instance ToExpr for MIR.Rvalue
deriving instance ToExpr for MIR.StatementKind
deriving instance ToExpr for MIR.SwitchTarget
deriving instance ToExpr for MIR.SwitchTargets
deriving instance ToExpr for MIR.SpannedOperand
deriving instance ToExpr for MIR.InlineAsmOptions
deriving instance ToExpr for MIR.InlineAsmTemplatePiece
deriving instance ToExpr for MIR.InlineAsmArch
deriving instance ToExpr for MIR.InlineAsmRegOrRegClass
deriving instance ToExpr for MIR.InlineAsmOperand
deriving instance ToExpr for MIR.InlineAsmTerminator
deriving instance ToExpr for MIR.AssertKind
deriving instance ToExpr for MIR.TerminatorKind
deriving instance ToExpr for MIR.SourceInfo
deriving instance ToExpr for MIR.Statement
deriving instance ToExpr for MIR.Terminator
deriving instance ToExpr for MIR.BasicBlock
deriving instance ToExpr for MIR.Body
deriving instance ToExpr for CallReifyReason
deriving instance ToExpr for CallShimKind
deriving instance ToExpr for CallInstanceKind
deriving instance ToExpr for CallInstance
deriving instance ToExpr for BodyIdentity
deriving instance ToExpr for LoadedBody

namespace DuplicatePrefix.RootBody

structure ReflectedRoot where
  functionInstance : CallInstance
  body : LoadedBody
  rootCallTargets : Array String
  copyHelper : LoadedBody
  copyPreconditionTarget : String
  preconditionHelper : LoadedBody
  deriving Repr

deriving instance ToExpr for ReflectedRoot

private def sourcePath (prepared : CallResolution.Prepared)
    (resolution : CallResolution.Resolution) : Except String String := do
  let some node := prepared.program.input.instances.find? (·.id == resolution.sourceInstanceId)
    | throw "compiler call has no instance node"
  match node.defPath with
  | some path => pure path
  | none => throw "compiler call instance has no exact def-path"

private def reflectRoot (path : String) : IO (Except String ReflectedRoot) := do
  let decoded ← Input.decodeFile path
  let decoded ← match decoded with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  let result := do
    let lowered ← Input.lowerProgram decoded.document
    let prepared ← CallResolution.prepare lowered
    let definition ← prepared.program.rootDefinitionId 0
    let fnInstance : CallInstance := ⟨.Item definition, #[]⟩
    let body ← CallResolution.loadedBodyOfInstance prepared fnInstance
    let mut paths := #[]
    for block in [2, 6, 7, 8] do
      let resolution ← CallResolution.atSite prepared ⟨body.identity.index, block⟩
      paths := paths.push (← sourcePath prepared resolution)
    let copyResolution ← CallResolution.atSite prepared ⟨body.identity.index, 8⟩
    let copyHelper ← CallResolution.loadedBodyOfInstance prepared copyResolution.callee
    let checkResolution ← CallResolution.atSite prepared ⟨copyHelper.identity.index, 4⟩
    let checkPath ← sourcePath prepared checkResolution
    let preconditionHelper ← CallResolution.loadedBodyOfInstance prepared checkResolution.callee
    pure ⟨fnInstance, body, paths, copyHelper, checkPath, preconditionHelper⟩
  return result

syntax (name := reflectDuplicatePrefix) "reflect_duplicate_prefix " str " as " ident : command

open Lean Elab Command in
elab_rules : command
  | `(reflect_duplicate_prefix $path:str as $name:ident) => do
    let reflected ← liftIO <| reflectRoot path.getString
    let reflected ← match reflected with
      | .ok value => pure value
      | .error message => throwErrorAt path "MIR lowering/reflection failed: {message}"
    let declName := (← getCurrNamespace) ++ name.getId
    let value ← liftTermElabM do
      pure (toExpr reflected)
    liftCoreM <| addDecl <| .defnDecl {
      name := declName
      levelParams := []
      type := mkConst ``ReflectedRoot
      value
      hints := .regular 0
      safety := .safe
    }

reflect_duplicate_prefix "examples/duplicate_prefix/input.json" as reflected

theorem root_body_shape :
    (reflected.body.body.argumentCount, reflected.body.body.locals.size,
      reflected.body.body.basicBlocks.size) = (2, 25, 11) := by
  rfl

theorem root_argument_type_ids :
    (reflected.body.body.locals[0]?, reflected.body.body.locals[1]?,
      reflected.body.body.locals[2]?) = (some 0, some 3, some 5) := by
  rfl

def statementKindAt (body : MIR.Body) (block statement : Nat) : Option StatementKind :=
  (body.basicBlocks[block]?).bind (fun bb => (bb.statements[statement]?).map Statement.kind)

private def blockTerminatorAt (body : MIR.Body) (block : Nat) : Option TerminatorKind :=
  (body.basicBlocks[block]?).map (fun bb => bb.terminator.kind)

theorem root_guard_zero_test :
    statementKindAt reflected.body.body 0 4 = some
      (.Assign ⟨4, #[]⟩ (.BinaryOp .Eq (.Move ⟨5, #[]⟩)
        (.Constant ⟨⟨3⟩, none, .Val (.Scalar (.Int 0 8)) 5⟩))) := by
  rfl

theorem root_count_copy :
    statementKindAt reflected.body.body 0 3 = some
      (.Assign ⟨5, #[]⟩ (.Use (.Copy ⟨2, #[]⟩) .Yes)) := by
  rfl

theorem root_guard_half_length :
    statementKindAt reflected.body.body 4 0 = some
      (.Assign ⟨10, #[]⟩ (.BinaryOp .Div (.Move ⟨11, #[]⟩)
        (.Constant ⟨⟨17⟩, none, .Val (.Scalar (.Int 2 8)) 5⟩))) := by
  rfl

theorem root_guard_comparison :
    statementKindAt reflected.body.body 4 2 = some
      (.Assign ⟨8, #[]⟩ (.BinaryOp .Gt (.Move ⟨9, #[]⟩) (.Move ⟨10, #[]⟩))) := by
  rfl

theorem root_guard_false_path :
    blockTerminatorAt reflected.body.body 4 =
      some (.SwitchInt (.Move ⟨8, #[]⟩) ⟨#[.Case 0 6], 5⟩) := by
  rfl

theorem root_call_targets :
    reflected.rootCallTargets = #[
      "core::slice::<impl [T]>::len",
      "core::slice::<impl [T]>::as_mut_ptr",
      "std::ptr::mut_ptr::<impl *mut T>::add",
      "std::ptr::copy_nonoverlapping"] := by
  rfl

private def isCopyIntrinsic (kind : Option StatementKind) : Bool :=
  match kind with
  | some (.Intrinsic (.CopyNonOverlapping _)) => true
  | _ => false

theorem copy_helper_has_actual_intrinsic :
    isCopyIntrinsic (statementKindAt reflected.copyHelper.body 7 8) = true := by
  rfl

theorem copy_helper_precondition_target : reflected.copyPreconditionTarget =
    "std::ptr::copy_nonoverlapping::precondition_check" := by
  rfl

theorem precondition_helper_body_present :
    reflected.preconditionHelper.body.basicBlocks.size = 16 := by
  rfl

-- These kernel audits are emitted by Lean during the example check.
#print axioms root_body_shape
#print axioms root_guard_zero_test
#print axioms root_count_copy
#print axioms root_guard_half_length
#print axioms root_guard_comparison
#print axioms root_guard_false_path
#print axioms root_call_targets
#print axioms copy_helper_has_actual_intrinsic
#print axioms copy_helper_precondition_target
#print axioms precondition_helper_body_present

/-- The actual root `LoadedBody` is the input to `Frame.create`; pointer and
length are installed as the source ABI pair, and `n` as a 64-bit scalar. This
constructor records frame/local values only. It is not `initFnCall`, does not
retag FnEntry arguments, and does not create or validate the backing allocation.
-/
def entryFrameForScalar {Prov : Type} (body : LoadedBody) (functionInstance : CallInstance)
    (extra : Extra) (returnPlace : RuntimeStackPlace Prov)
    (initialSpan : SpanRef) (localsIdentity : LocalsIdentity)
    (target : TargetDataLayout) (pointerScalar : Scalar Prov) (length n : UInt64) :
    Except String (Frame Prov LocalLayout Extra) := do
  if target.pointerWidth != .w64 then
    throw "duplicate_prefix entry values require the exported x86_64 target"
  let metadata := Scalar.fromScalarInt (ScalarInt.ofUInt64 length)
  let count := Scalar.fromScalarInt (ScalarInt.ofUInt64 n)
  let frame := Frame.create body functionInstance extra (.stop true)
    returnPlace initialSpan localsIdentity
  let frame ← (frame.replaceLocalValue 1 (.live (.immediate (.scalarPair pointerScalar metadata))))
    |>.mapError reprStr
  let frame ← (frame.replaceLocalValue 2 (.live (.immediate (.scalar count))))
    |>.mapError reprStr
  (frame.setLocation (.mir ⟨0, 0⟩)).mapError reprStr

/-- Pointer convenience form for inputs carrying an explicit provenance-bearing
pointer. The scalar constructor also admits raw integer pointer scalars used
for empty slices, including dangling non-null values without provenance. -/
def entryFrameFor {Prov : Type} (body : LoadedBody) (functionInstance : CallInstance)
    (extra : Extra) (returnPlace : RuntimeStackPlace Prov)
    (initialSpan : SpanRef) (localsIdentity : LocalsIdentity)
    (target : TargetDataLayout) (buffer : Pointer Prov) (length n : UInt64) :
    Except String (Frame Prov LocalLayout Extra) :=
  entryFrameForScalar body functionInstance extra returnPlace initialSpan localsIdentity
    target (Scalar.fromPointer target buffer) length n

/-- The concrete constructor succeeds for the reflected root body under the
exported 64-bit target. This proves only stack-frame/local installation, not
the memory allocation, retag, or call-entry lifecycle. -/
theorem entryFrameForScalar_succeeds {Prov : Type} (extra : Extra)
    (returnPlace : RuntimeStackPlace Prov) (initialSpan : SpanRef)
    (localsIdentity : LocalsIdentity) (target : TargetDataLayout)
    (pointerScalar : Scalar Prov) (length n : UInt64)
    (hwidth : target.pointerWidth = .w64) :
    ∃ frame,
      entryFrameForScalar reflected.body reflected.functionInstance extra
        returnPlace initialSpan localsIdentity target pointerScalar length n = .ok frame ∧
      ∃ layout1 layout2,
        frame.getLocal 1 = .ok { value := .live (.immediate (.scalarPair
          pointerScalar
          (Scalar.fromScalarInt (ScalarInt.ofUInt64 length)))), layout := layout1 } ∧
        frame.getLocal 2 = .ok { value := .live (.immediate (.scalar
          (Scalar.fromScalarInt (ScalarInt.ofUInt64 n)))), layout := layout2 } := by
  have hlocals : reflected.body.body.locals.size = 25 := by rfl
  have hblocks : reflected.body.body.basicBlocks.size = 11 := by rfl
  have hnotWidth : (target.pointerWidth != .w64) = false := by simp [hwidth]
  let frame0 : Frame Prov LocalLayout Extra :=
    Frame.create reflected.body reflected.functionInstance extra (.stop true)
    returnPlace initialSpan localsIdentity
  have hframe0 : Frame.create reflected.body reflected.functionInstance extra (.stop true)
      returnPlace initialSpan localsIdentity = frame0 := rfl
  let value1 := LocalValue.live (.immediate (.scalarPair pointerScalar
    (Scalar.fromScalarInt (ScalarInt.ofUInt64 length))))
  have hbound1 : 1 < frame0.locals.size := by simp [frame0, Frame.create, hlocals]
  let frame1 := { frame0 with locals :=
    (frame0.locals.set 1 { value := value1, layout := frame0.locals[1].layout } hbound1) }
  have hset1 : frame0.replaceLocalValue 1 value1 = .ok frame1 :=
    FrameFacts.replace_value frame0 1 value1 hbound1
  have hsize1 : frame1.locals.size = 25 := by simp [frame1, frame0, Frame.create, hlocals]
  let value2 : LocalValue Prov := LocalValue.live (.immediate (.scalar
    (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))))
  have hbound2 : 2 < frame1.locals.size := by rw [hsize1]; decide
  let frame2 : Frame Prov LocalLayout Extra := { frame1 with locals :=
    (frame1.locals.set 2 { value := value2, layout := frame1.locals[2].layout } hbound2) }
  have hset2 : frame1.replaceLocalValue 2 value2 = .ok frame2 :=
    FrameFacts.replace_value frame1 2 value2 hbound2
  have hsize2 : frame2.locals.size = 25 := by simp [frame2, frame1, frame0, Frame.create, hlocals]
  let frame3 := { frame2 with location := .mir ⟨0, 0⟩ }
  have hloc : frame2.setLocation (.mir ⟨0, 0⟩) = .ok frame3 := by
    simp [Frame.setLocation, frame3, frame2, frame1, frame0, Frame.create,
      hblocks, hlocals]
    rfl
  refine ⟨frame3, ?_, ?_⟩
  unfold entryFrameForScalar
  simp only [hnotWidth, Bool.false_eq_true, ite_false]
  simp [hframe0, value1, value2, hset1, hset2, hloc, Except.mapError, Except.bind,
    Bind.bind]
  · obtain ⟨layout1, hget1⟩ :=
      FrameFacts.get_replaced_value frame0 frame1 1 value1 hset1
    obtain ⟨layout2, hget2⟩ :=
      FrameFacts.get_replaced_value frame1 frame2 2 value2 hset2
    have hget1After := FrameFacts.get_other_value frame1 frame2 2 1
      value2 (by decide) hset2
    have hframe3 : frame3 = { frame2 with location := .mir ⟨0, 0⟩ } := by
      have heq : (Except.ok ({ frame2 with location := .mir ⟨0, 0⟩ } :
          Frame Prov LocalLayout Extra) : Except StepError (Frame Prov LocalLayout Extra)) =
          Except.ok frame3 := by
        simpa [Frame.setLocation, frame3, frame2, frame1, frame0, Frame.create,
          hblocks, hlocals] using hloc
      cases heq
      rfl
    have hlocal1 : frame3.getLocal 1 = frame2.getLocal 1 := by
      rw [hframe3]
      rfl
    have hlocal2 : frame3.getLocal 2 = frame2.getLocal 2 := by
      rw [hframe3]
      rfl
    refine ⟨layout1, layout2, ?_, ?_⟩
    · exact hlocal1.trans (hget1After.trans hget1)
    · exact hlocal2.trans hget2

#print axioms entryFrameForScalar_succeeds

theorem entryFrameFor_succeeds {Prov : Type} (extra : Extra)
    (returnPlace : RuntimeStackPlace Prov) (initialSpan : SpanRef)
    (localsIdentity : LocalsIdentity) (target : TargetDataLayout)
    (buffer : Pointer Prov) (length n : UInt64)
    (hwidth : target.pointerWidth = .w64) :
    ∃ frame,
      entryFrameFor reflected.body reflected.functionInstance extra
        returnPlace initialSpan localsIdentity target buffer length n = .ok frame ∧
      ∃ layout1 layout2,
        frame.getLocal 1 = .ok { value := .live (.immediate (.scalarPair
          (Scalar.fromPointer target buffer)
          (Scalar.fromScalarInt (ScalarInt.ofUInt64 length)))), layout := layout1 } ∧
        frame.getLocal 2 = .ok { value := .live (.immediate (.scalar
          (Scalar.fromScalarInt (ScalarInt.ofUInt64 n)))), layout := layout2 } := by
  obtain ⟨frame, success, locals⟩ := entryFrameForScalar_succeeds extra returnPlace
    initialSpan localsIdentity target (Scalar.fromPointer target buffer) length n hwidth
  exact ⟨frame, by simpa [entryFrameFor] using success, locals⟩

#print axioms entryFrameFor_succeeds

end DuplicatePrefix.RootBody
