import Miri.MIR.Syntax

/-! Typed traversal of the executable MIR projection. Pinned rustc derives
TypeFoldable for mir::Body and its syntax records (mir/mod.rs:205 onward).
Every represented type, type-system constant, region and runtime constant
value is visited. Source scopes, coroutine witnesses and other exporter input
metadata are outside MIR.Body and require their own instantiation. -/
namespace Miri.MIR.Fold

structure Hooks where
  ty : TyId → Except String TyId
  constant : TypeConstId → Except String TypeConstId
  region : Region → Except String Region
  value : ConstValue → Except String ConstValue

def identity : Hooks := ⟨pure,pure,pure,pure⟩

def genericArg (h : Hooks) : GenericArg → Except String GenericArg
  | .Type ty => return .Type (← h.ty ty)
  | .Lifetime region => return .Lifetime (← h.region region)
  | .Const value => return .Const (← h.constant value)

def projection (h : Hooks) : ProjectionElem → Except String ProjectionElem
  | .Field index ty => return .Field index (← h.ty ty)
  | .OpaqueCast ty => return .OpaqueCast (← h.ty ty)
  | .UnwrapUnsafeBinder ty => return .UnwrapUnsafeBinder (← h.ty ty)
  | other => pure other

def place (h : Hooks) (source : Place) : Except String Place :=
  return { source with projection := ← source.projection.mapM (projection h) }

def constantOperand (h : Hooks) (source : ConstOperand) : Except String ConstOperand := do
  let .Val value ty := source.value
  return { source with value := .Val (← h.value value) (← h.ty ty) }

def operand (h : Hooks) : Operand → Except String Operand
  | .Copy source => return .Copy (← place h source)
  | .Move source => return .Move (← place h source)
  | .Constant source => return .Constant (← constantOperand h source)
  | .RuntimeChecks check => pure (.RuntimeChecks check)

def aggregate (h : Hooks) : AggregateKind → Except String AggregateKind
  | .Array ty => return .Array (← h.ty ty)
  | .Tuple => pure .Tuple
  | .Adt definition variant args annotation active =>
    return .Adt definition variant (← args.mapM (genericArg h)) annotation active
  | .Closure definition args => return .Closure definition (← args.mapM (genericArg h))
  | .Coroutine definition args => return .Coroutine definition (← args.mapM (genericArg h))
  | .CoroutineClosure definition args => return .CoroutineClosure definition (← args.mapM (genericArg h))
  | .RawPtr pointee mutability => return .RawPtr (← h.ty pointee) mutability

def rvalue (h : Hooks) : Rvalue → Except String Rvalue
  | .Use value retag => return .Use (← operand h value) retag
  | .Repeat value count => return .Repeat (← operand h value) (← h.constant count)
  | .Ref region borrow source => return .Ref (← h.region region) borrow (← place h source)
  | .ThreadLocalRef definition => pure (.ThreadLocalRef definition)
  | .RawPtr kind source => return .RawPtr kind (← place h source)
  | .Cast kind source ty => return .Cast kind (← operand h source) (← h.ty ty)
  | .BinaryOp operator left right => return .BinaryOp operator (← operand h left) (← operand h right)
  | .UnaryOp operator source => return .UnaryOp operator (← operand h source)
  | .Discriminant source => return .Discriminant (← place h source)
  | .Aggregate kind values => return .Aggregate (← aggregate h kind) (← values.mapM (operand h))
  | .CopyForDeref source => return .CopyForDeref (← place h source)
  | .WrapUnsafeBinder source ty => return .WrapUnsafeBinder (← operand h source) (← h.ty ty)
  | .Reborrow ty mutability source => return .Reborrow (← h.ty ty) mutability (← place h source)

def intrinsic (h : Hooks) : NonDivergingIntrinsic → Except String NonDivergingIntrinsic
  | .Assume source => return .Assume (← operand h source)
  | .CopyNonOverlapping args => return .CopyNonOverlapping ⟨← operand h args.source, ← operand h args.destination, ← operand h args.count⟩

def statementKind (h : Hooks) : StatementKind → Except String StatementKind
  | .Assign destination value => return .Assign (← place h destination) (← rvalue h value)
  | .FakeRead cause source => return .FakeRead cause (← place h source)
  | .SetDiscriminant source variant => return .SetDiscriminant (← place h source) variant
  | .PlaceMention source => return .PlaceMention (← place h source)
  | .AscribeUserType source projection variance => return .AscribeUserType (← place h source) projection variance
  | .Intrinsic source => return .Intrinsic (← intrinsic h source)
  | .BackwardIncompatibleDropHint source reason => return .BackwardIncompatibleDropHint (← place h source) reason
  | .StorageLive localId => pure (.StorageLive localId)
  | .StorageDead localId => pure (.StorageDead localId)
  | .Coverage kind => pure (.Coverage kind)
  | .ConstEvalCounter => pure .ConstEvalCounter
  | .Nop => pure .Nop

def assertKind (h : Hooks) : AssertKind → Except String AssertKind
  | .BoundsCheck length index => return .BoundsCheck (← operand h length) (← operand h index)
  | .Overflow operator left right => return .Overflow operator (← operand h left) (← operand h right)
  | .OverflowNeg source => return .OverflowNeg (← operand h source)
  | .DivisionByZero source => return .DivisionByZero (← operand h source)
  | .RemainderByZero source => return .RemainderByZero (← operand h source)
  | .MisalignedPointerDereference required found =>
    return .MisalignedPointerDereference (← operand h required) (← operand h found)
  | .InvalidEnumConstruction source => return .InvalidEnumConstruction (← operand h source)
  | .ResumedAfterReturn kind => pure (.ResumedAfterReturn kind)
  | .ResumedAfterPanic kind => pure (.ResumedAfterPanic kind)
  | .ResumedAfterDrop kind => pure (.ResumedAfterDrop kind)
  | .NullPointerDereference => pure .NullPointerDereference
  | .NullReferenceConstructed => pure .NullReferenceConstructed

def spannedOperand (h : Hooks) (source : SpannedOperand) : Except String SpannedOperand :=
  return { source with operand := ← operand h source.operand }

def asmOperand (h : Hooks) : InlineAsmOperand → Except String InlineAsmOperand
  | .In register value => return .In register (← operand h value)
  | .Out register late output => return .Out register late (← output.mapM (place h))
  | .InOut register late input output =>
    return .InOut register late (← operand h input) (← output.mapM (place h))
  | .Const value => return .Const (← constantOperand h value)
  | .SymFn value => return .SymFn (← constantOperand h value)
  | .SymStatic definition => pure (.SymStatic definition)
  | .Label target => pure (.Label target)

def terminatorKind (h : Hooks) : TerminatorKind → Except String TerminatorKind
  | .SwitchInt discriminant targets => return .SwitchInt (← operand h discriminant) targets
  | .Drop source target unwind replace asyncDrop =>
    return .Drop (← place h source) target unwind replace asyncDrop
  | .Call function args destination target unwind source span =>
    return .Call (← operand h function) (← args.mapM (spannedOperand h))
      (← place h destination) target unwind source span
  | .TailCall function args span =>
    return .TailCall (← operand h function) (← args.mapM (spannedOperand h)) span
  | .Assert condition expected message target unwind =>
    return .Assert (← operand h condition) expected (← assertKind h message) target unwind
  | .Yield value resume argument drop => return .Yield (← operand h value) resume (← place h argument) drop
  | .InlineAsm source => return .InlineAsm { source with operands := ← source.operands.mapM (asmOperand h) }
  | .Goto target hints => pure (.Goto target hints)
  | .UnwindResume => pure .UnwindResume
  | .UnwindTerminate reason => pure (.UnwindTerminate reason)
  | .Return => pure .Return
  | .Unreachable => pure .Unreachable
  | .CoroutineDrop => pure .CoroutineDrop
  | .FalseEdge real imaginary => pure (.FalseEdge real imaginary)
  | .FalseUnwind target unwind => pure (.FalseUnwind target unwind)

def body (h : Hooks) (source : Body) : Except String Body := do
  let locals ← source.locals.mapM h.ty
  let blocks ← source.basicBlocks.mapM fun block => do
    let statements ← block.statements.mapM fun statement => do
      return { statement with kind := ← statementKind h statement.kind }
    let terminator := block.terminator
    let terminator ← pure { terminator with kind := ← terminatorKind h terminator.kind }
    return { block with statements, terminator }
  return { source with locals, basicBlocks := blocks }

end Miri.MIR.Fold
