import Miri.Input.Model.Catalogs
import Miri.MIR.Syntax

namespace Miri.Input.DecodeMIR
open Miri.MIR

/-- Scalar bits cannot be assigned a machine byte width until the complete type
and layout tables have been read. Other constant payloads already have their
final representation but still contain numeric references to validate. -/
inductive DraftConstValue where
  | ready (value : MIR.ConstValue)
  | scalar (bits : Nat)

structure DraftConstant where
  typeId : Nat
  span : MIR.SpanRef
  userType : Option Nat
  evaluated : DraftConstValue

/- The draft duplicates only the MIR spine that contains constants and the
place metadata needed for node facts. Operators and other leaves reuse MIR
constructors; numeric pool IDs never expand into recursive table values. -/
namespace Draft

structure Place where
  value : MIR.Place
  typeId : Nat
  projectionTypes : Array Nat

abbrev ConstOperand := DraftConstant

inductive Operand where
  | Copy (place : Place)
  | Move (place : Place)
  | Constant (constant : ConstOperand)
  | RuntimeChecks (check : RuntimeChecks)


structure CopyNonOverlapping where
  source : Operand
  destination : Operand
  count : Operand


inductive NonDivergingIntrinsic where
  | Assume (condition : Operand)
  | CopyNonOverlapping (args : CopyNonOverlapping)


inductive Rvalue where
  | Use (operand : Operand) (retag : WithRetag)
  | Repeat (operand : Operand) (count : TypeConstId)
  | Ref (region : Region) (borrow : BorrowKind) (place : Place)
  | ThreadLocalRef (entry : Catalog.ThreadLocal)
  | RawPtr (kind : RawPtrKind) (place : Place)
  | Cast (kind : CastKind) (operand : Operand) (targetType : TyId)
      (upcast : Option DynamicUpcastEvidence)
  | BinaryOp (operator : BinOp) (left right : Operand)
  | UnaryOp (operator : UnOp) (operand : Operand)
  | Discriminant (place : Place)
  | Aggregate (kind : AggregateKind) (operands : Array Operand)
  | CopyForDeref (place : Place)
  | WrapUnsafeBinder (operand : Operand) (targetType : TyId)
  | Reborrow (ty : TyId) (mutability : Mutability) (place : Place)


inductive StatementKind where
  | Assign (destination : Place) (value : Rvalue)
  | FakeRead (cause : FakeReadCause) (place : Place)
  | SetDiscriminant (place : Place) (variant : VariantIndex)
  | StorageLive (localId : LocalId)
  | StorageDead (localId : LocalId)
  | PlaceMention (place : Place)
  | AscribeUserType (place : Place) (projection : UserTypeProjection) (variance : Variance)
  | Coverage (coverage : CoverageKind)
  | Intrinsic (intrinsic : NonDivergingIntrinsic)
  | ConstEvalCounter
  | Nop
  | BackwardIncompatibleDropHint (place : Place) (reason : BackwardIncompatibleDropReason)


structure SpannedOperand where
  span : SpanRef
  operand : Operand


inductive InlineAsmOperand where
  | In (register : InlineAsmRegOrRegClass) (value : Operand)
  | Out (register : InlineAsmRegOrRegClass) (late : Bool) (place : Option Place)
  | InOut (register : InlineAsmRegOrRegClass) (late : Bool) (input : Operand)
      (output : Option Place)
  | Const (value : ConstOperand)
  | SymFn (value : ConstOperand)
  | SymStatic (definition : DefId)
  | Label (targetIndex : Nat)


structure InlineAsmTerminator where
  asmMacro : InlineAsmMacro
  template : Array InlineAsmTemplatePiece
  operands : Array InlineAsmOperand
  options : InlineAsmOptions
  lineSpans : Array SpanRef
  targets : Array BasicBlockId
  unwind : UnwindAction


inductive AssertKind where
  | BoundsCheck (length index : Operand)
  | Overflow (operator : BinOp) (left right : Operand)
  | OverflowNeg (operand : Operand)
  | DivisionByZero (operand : Operand)
  | RemainderByZero (operand : Operand)
  | ResumedAfterReturn (coroutine : CoroutineKind)
  | ResumedAfterPanic (coroutine : CoroutineKind)
  | ResumedAfterDrop (coroutine : CoroutineKind)
  | MisalignedPointerDereference (required found : Operand)
  | NullPointerDereference
  | NullReferenceConstructed
  | InvalidEnumConstruction (operand : Operand)


inductive TerminatorKind where
  | Goto (target : BasicBlockId) (loopHints : Array LoopHintAttr)
  | SwitchInt (discriminant : Operand) (targets : SwitchTargets)
  | UnwindResume
  | UnwindTerminate (reason : UnwindTerminateReason)
  | Return
  | Unreachable
  | Drop (place : Place) (target : BasicBlockId) (unwind : UnwindAction)
      (replace : Bool) (asyncDrop : Option BasicBlockId)
  | Call (function : Operand) (arguments : Array SpannedOperand) (destination : Place)
      (target : Option BasicBlockId) (unwind : UnwindAction) (source : CallSource)
      (functionSpan : SpanRef)
  | TailCall (function : Operand) (arguments : Array SpannedOperand) (functionSpan : SpanRef)
  | Assert (condition : Operand) (expected : Bool) (message : AssertKind)
      (target : BasicBlockId) (unwind : UnwindAction)
  | Yield (value : Operand) (resume : BasicBlockId) (resumeArgument : Place)
      (drop : Option BasicBlockId)
  | CoroutineDrop
  | FalseEdge (realTarget imaginaryTarget : BasicBlockId)
  | FalseUnwind (realTarget : BasicBlockId) (unwind : UnwindAction)
  | InlineAsm (asm : InlineAsmTerminator)


structure Statement where
  sourceInfo : MIR.SourceInfo
  kind : StatementKind


structure Terminator where
  sourceInfo : MIR.SourceInfo
  kind : TerminatorKind

  evidence : Option CallResolutionEvidence

structure BasicBlock where
  statements : Array Statement
  terminator : Terminator
  cleanup : Bool


end Draft

structure DraftBody where
  sourcePath : String := ""
  phase : MIR.MirPhase
  argumentCount : Nat
  spreadArgument : Option Nat
  locals : Array LocalDecl
  blocks : Array Draft.BasicBlock
  definitionId : Option Nat
  defPath : Option String
  spanId : Nat
  preambleDefSpanId : Nat
  injectionPhase : Option MIR.MirPhase
  instanceId : Nat
  sourceScopes : Array SourceScope
  backtraceSpans : Array BacktraceSpan
  requiredConsts : Array DraftConstant
  promotedBodies : Array PromotedBody

end Miri.Input.DecodeMIR
