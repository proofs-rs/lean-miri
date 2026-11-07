import Miri.MIR.SyntaxTables

/-! A checked structural observation of table-backed MIR, for specifications and
independent comparisons with source-shaped MIR. The evaluator keeps IDs and uses
its own checked lookups; it never invokes these observations. -/
namespace Miri.MIR.Contents

private def entry (table : SharedTable α) (id : Nat) (kind : String) : Except String α :=
  (table.lookup id).mapError fun id => s!"invalid MIR {kind} ID {id}"

def place (tables : SyntaxTables) (id : PlaceId) : Except String Place := do
  let node ← entry tables.places id.index "place"
  let ids ← entry tables.projectionLists node.projection.index "projection list"
  return ⟨node.localId, ← ids.mapM (fun id => entry tables.projections id.index "projection")⟩

def constant (tables : SyntaxTables) (id : ConstantId) : Except String ConstOperand := do
  return (← entry tables.constants id.index "constant").operand

def operand (tables : SyntaxTables) (id : OperandId) : Except String Operand := do
  match ← entry tables.operands id.index "operand" with
  | .Copy id => return .Copy (← place tables id)
  | .Move id => return .Move (← place tables id)
  | .Constant id => return .Constant (← constant tables id)
  | .RuntimeChecks check => return .RuntimeChecks check

def aggregate (tables : SyntaxTables) (node : AggregateNode) : Except String AggregateKind := do
  let args := fun id => entry tables.arguments id "generic arguments"
  match node with
  | .Array ty => return .Array ty
  | .Tuple => return .Tuple
  | .Adt definition variant id user active => return .Adt definition variant (← args id) user active
  | .Closure definition id => return .Closure definition (← args id)
  | .Coroutine definition id => return .Coroutine definition (← args id)
  | .CoroutineClosure definition id => return .CoroutineClosure definition (← args id)
  | .RawPtr ty mutability => return .RawPtr ty mutability

def rvalue (tables : SyntaxTables) (typeConstants : Array TypeConst) (id : RvalueId) : Except String Rvalue := do
  let op := operand tables
  let pl := place tables
  match ← entry tables.rvalues id.index "rvalue" with
  | .Use value retag => return .Use (← op value) retag
  | .Repeat value count =>
    let some count := typeConstants[count]? | throw "invalid MIR repeat type constant"
    return .Repeat (← op value) count
  | .Ref region borrow value => return .Ref (← entry tables.regions region "region") borrow (← pl value)
  | .ThreadLocalRef definition => return .ThreadLocalRef definition
  | .RawPtr kind value => return .RawPtr kind (← pl value)
  | .Cast kind value ty => return .Cast kind (← op value) ty
  | .BinaryOp kind left right => return .BinaryOp kind (← op left) (← op right)
  | .UnaryOp kind value => return .UnaryOp kind (← op value)
  | .Discriminant value => return .Discriminant (← pl value)
  | .Aggregate kind values =>
    let values ← entry tables.operandLists values.index "operand list"
    return .Aggregate (← aggregate tables kind) (← values.mapM op)
  | .CopyForDeref value => return .CopyForDeref (← pl value)
  | .WrapUnsafeBinder value ty => return .WrapUnsafeBinder (← op value) ty
  | .Reborrow ty mutability value => return .Reborrow ty mutability (← pl value)

def intrinsic (tables : SyntaxTables) (node : IntrinsicNode) : Except String NonDivergingIntrinsic := do
  match node with
  | .Assume condition => return .Assume (← operand tables condition)
  | .CopyNonOverlapping args => return .CopyNonOverlapping ⟨← operand tables args.source, ← operand tables args.destination, ← operand tables args.count⟩

def statement (tables : SyntaxTables) (typeConstants : Array TypeConst) (id : StatementId) : Except String Statement := do
  let node ← entry tables.statements id.index "statement"
  let pl := place tables
  let kind ← (show Except String StatementKind from do
    match node.kind with
    | .Assign dest value => return .Assign (← pl dest) (← rvalue tables typeConstants value)
    | .FakeRead cause value => return .FakeRead cause (← pl value)
    | .SetDiscriminant value variant => return .SetDiscriminant (← pl value) variant
    | .StorageLive id => pure (.StorageLive id)
    | .StorageDead id => pure (.StorageDead id)
    | .PlaceMention value => return .PlaceMention (← pl value)
    | .AscribeUserType value projection variance => return .AscribeUserType (← pl value) projection variance
    | .Coverage coverage => pure (.Coverage coverage)
    | .Intrinsic value => return .Intrinsic (← intrinsic tables value)
    | .ConstEvalCounter => pure .ConstEvalCounter
    | .Nop => pure .Nop
    | .BackwardIncompatibleDropHint value reason => return .BackwardIncompatibleDropHint (← pl value) reason
  )
  return ⟨node.sourceInfo, kind⟩

def assertion (tables : SyntaxTables) (node : AssertNode) : Except String AssertKind := do
  let op := operand tables
  match node with
  | .BoundsCheck length index => return .BoundsCheck (← op length) (← op index)
  | .Overflow kind left right => return .Overflow kind (← op left) (← op right)
  | .OverflowNeg value => return .OverflowNeg (← op value)
  | .DivisionByZero value => return .DivisionByZero (← op value)
  | .RemainderByZero value => return .RemainderByZero (← op value)
  | .ResumedAfterReturn kind => pure (.ResumedAfterReturn kind)
  | .ResumedAfterPanic kind => pure (.ResumedAfterPanic kind)
  | .ResumedAfterDrop kind => pure (.ResumedAfterDrop kind)
  | .MisalignedPointerDereference required found => return .MisalignedPointerDereference (← op required) (← op found)
  | .NullPointerDereference => pure .NullPointerDereference
  | .NullReferenceConstructed => pure .NullReferenceConstructed
  | .InvalidEnumConstruction value => return .InvalidEnumConstruction (← op value)

def asmOperand (tables : SyntaxTables) (node : InlineAsmOperandNode) : Except String InlineAsmOperand := do
  match node with
  | .In register value => return .In register (← operand tables value)
  | .Out register late value => return .Out register late (← value.mapM (place tables))
  | .InOut register late input output => return .InOut register late (← operand tables input) (← output.mapM (place tables))
  | .Const value => return .Const (← constant tables value)
  | .SymFn value => return .SymFn (← constant tables value)
  | .SymStatic definition => pure (.SymStatic definition)
  | .Label target => pure (.Label target)

def inlineAsm (tables : SyntaxTables) (node : InlineAsmNode) : Except String InlineAsmTerminator := do
  return ⟨node.asmMacro, node.template, ← node.operands.mapM (asmOperand tables),
    node.options, node.lineSpans, node.targets, node.unwind⟩

def spannedOperand (tables : SyntaxTables) (node : SpannedOperandNode) : Except String SpannedOperand := do
  return ⟨node.span, ← operand tables node.operand⟩

def terminator (tables : SyntaxTables) (id : TerminatorId) : Except String Terminator := do
  let node ← entry tables.terminators id.index "terminator"
  let pl := place tables
  let op := operand tables
  let kind ← (show Except String TerminatorKind from do
    match node.kind with
    | .Goto target hints => pure (.Goto target hints)
    | .SwitchInt value targets => return .SwitchInt (← op value) targets
    | .UnwindResume => pure .UnwindResume
    | .UnwindTerminate reason => pure (.UnwindTerminate reason)
    | .Return => pure .Return
    | .Unreachable => pure .Unreachable
    | .Drop value target unwind replace asyncDrop => return .Drop (← pl value) target unwind replace asyncDrop
    | .Call fn args dest target unwind source span => return .Call (← op fn) (← args.mapM (spannedOperand tables)) (← pl dest) target unwind source span
    | .TailCall fn args span => return .TailCall (← op fn) (← args.mapM (spannedOperand tables)) span
    | .Assert value expected message target unwind => return .Assert (← op value) expected (← assertion tables message) target unwind
    | .Yield value resume argument drop => return .Yield (← op value) resume (← pl argument) drop
    | .CoroutineDrop => pure .CoroutineDrop
    | .FalseEdge real imaginary => pure (.FalseEdge real imaginary)
    | .FalseUnwind real unwind => pure (.FalseUnwind real unwind)
    | .InlineAsm asm => return .InlineAsm (← inlineAsm tables asm)
  )
  return ⟨node.sourceInfo, kind⟩

def block (tables : SyntaxTables) (typeConstants : Array TypeConst) (id : BlockNodeId) : Except String BasicBlock := do
  let node ← entry tables.blocks id.index "block"
  return ⟨← node.statements.mapM (statement tables typeConstants), ← terminator tables node.terminator, node.cleanup⟩

def body (tables : SyntaxTables) (typeConstants : Array TypeConst) (node : BodyNode) : Except String Body := do
  return ⟨node.phase, node.argumentCount, node.spreadArgument, node.locals,
    ← node.basicBlocks.mapM (block tables typeConstants)⟩

end Miri.MIR.Contents
