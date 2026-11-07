import Miri.Input.Reader.ReferenceBounds

namespace Miri.Input.Reader.PlaceTypeReader
open Miri.MIR

private abbrev Pairs := Std.HashSet (Nat × Nat)
private structure State where
  types : SharedTable TyId
  constants : Array (ConstantId × ConstantId) := #[]
  constantIndex : Std.HashMap Nat ConstantId := {}
  operands : Pairs := {}
  rvalues : Pairs := {}
  statements : Pairs := {}
  terminators : Pairs := {}
  blocks : Pairs := {}
private abbrev Pairing := StateT State (Except String)

private def entry (table : SharedTable A) (id : Nat) (kind : String) : Except String A :=
  (table.lookup id).mapError (fun id => s!"invalid normalized MIR {kind} ID {id}")

private def once (getPairs : State → Pairs) (putPairs : State → Pairs → State)
    (a b : Nat) (action : Pairing Unit) : Pairing Unit := do
  let state ← get
  if (getPairs state).contains (a,b) then return
  set (putPairs state ((getPairs state).insert (a,b)))
  action

private def array (a : Array A) (b : Array B) (pair : A → B → Pairing Unit) : Pairing Unit := do
  unless a.size == b.size do throw "normalization changed MIR list length"
  for index in [:a.size] do
    let some left := a[index]? | throw "source MIR list entry absent"
    let some right := b[index]? | throw "normalized MIR list entry absent"
    pair left right

private def place (tables : SyntaxTables) (a b : PlaceId) : Pairing Unit := do
  let source ← entry tables.places a.index "place"
  let normalized ← entry tables.places b.index "place"
  unless source.localId == normalized.localId do throw "normalization changed place local"
  let state ← get
  let some slot := state.types[a.index]? | throw "source place type slot absent"
  if let some previous := slot then
    unless previous == normalized.typeId do throw "source place has conflicting normalized types"
  else if bound : a.index < state.types.size then
    set {state with types := state.types.set a.index (some normalized.typeId) bound}
  else throw "source place type slot absent"

private def optionalPlace (tables : SyntaxTables) : Option PlaceId → Option PlaceId → Pairing Unit
  | none, none => pure ()
  | some a, some b => place tables a b
  | _, _ => throw "normalization changed optional place"

private def constant (tables : SyntaxTables) (a b : ConstantId) : Pairing Unit := do
  let source ← entry tables.constants a.index "constant"
  let normalized ← entry tables.constants b.index "constant"
  unless source.operand.span == normalized.operand.span do throw "normalization changed constant span"
  let state ← get
  if let some previous := state.constantIndex[a.index]? then
    unless (← entry tables.constants previous.index "constant") == normalized do
      throw "source constant has conflicting normalization in one body"
  else
    set {state with constants := state.constants.push (a,b), constantIndex := state.constantIndex.insert a.index b}

private def operand (tables : SyntaxTables) (a b : OperandId) : Pairing Unit :=
  once (·.operands) (fun state operands => {state with operands}) a.index b.index do
    match ← entry tables.operands a.index "operand", ← entry tables.operands b.index "operand" with
    | .Copy a, .Copy b | .Move a, .Move b => place tables a b
    | .Constant a, .Constant b => constant tables a b
    | .RuntimeChecks _, .RuntimeChecks _ => pure ()
    | _, _ => throw "normalization changed operand constructor"

private def rvalue (tables : SyntaxTables) (a b : RvalueId) : Pairing Unit :=
  once (·.rvalues) (fun state rvalues => {state with rvalues}) a.index b.index do
    match ← entry tables.rvalues a.index "rvalue", ← entry tables.rvalues b.index "rvalue" with
    | .Use a _, .Use b _ | .Repeat a _, .Repeat b _ | .Cast _ a _, .Cast _ b _
    | .UnaryOp _ a, .UnaryOp _ b | .WrapUnsafeBinder a _, .WrapUnsafeBinder b _ => operand tables a b
    | .Ref _ _ a, .Ref _ _ b | .RawPtr _ a, .RawPtr _ b | .Discriminant a, .Discriminant b
    | .CopyForDeref a, .CopyForDeref b | .Reborrow _ _ a, .Reborrow _ _ b => place tables a b
    | .BinaryOp _ a c, .BinaryOp _ b d => operand tables a b; operand tables c d
    | .Aggregate _ a, .Aggregate _ b =>
      array (← entry tables.operandLists a.index "operand list")
        (← entry tables.operandLists b.index "operand list") (operand tables)
    | .ThreadLocalRef _, .ThreadLocalRef _ => pure ()
    | _, _ => throw "normalization changed rvalue constructor"

private def intrinsic (tables : SyntaxTables) : IntrinsicNode → IntrinsicNode → Pairing Unit
  | .Assume a, .Assume b => operand tables a b
  | .CopyNonOverlapping a, .CopyNonOverlapping b => do
    operand tables a.source b.source
    operand tables a.destination b.destination
    operand tables a.count b.count
  | _, _ => throw "normalization changed intrinsic constructor"

private def statement (tables : SyntaxTables) (a b : StatementId) : Pairing Unit :=
  once (·.statements) (fun state statements => {state with statements}) a.index b.index do
    match (← entry tables.statements a.index "statement").kind,
        (← entry tables.statements b.index "statement").kind with
    | .Assign a c, .Assign b d => place tables a b; rvalue tables c d
    | .FakeRead _ a, .FakeRead _ b | .SetDiscriminant a _, .SetDiscriminant b _
    | .PlaceMention a, .PlaceMention b | .AscribeUserType a _ _, .AscribeUserType b _ _
    | .BackwardIncompatibleDropHint a _, .BackwardIncompatibleDropHint b _ => place tables a b
    | .Intrinsic a, .Intrinsic b => intrinsic tables a b
    | .StorageLive _, .StorageLive _ | .StorageDead _, .StorageDead _
    | .Coverage _, .Coverage _ | .ConstEvalCounter, .ConstEvalCounter | .Nop, .Nop => pure ()
    | _, _ => throw "normalization changed statement constructor"

private def assertion (tables : SyntaxTables) : AssertNode → AssertNode → Pairing Unit
  | .BoundsCheck a c, .BoundsCheck b d | .Overflow _ a c, .Overflow _ b d
  | .MisalignedPointerDereference a c, .MisalignedPointerDereference b d => do
    operand tables a b; operand tables c d
  | .OverflowNeg a, .OverflowNeg b | .DivisionByZero a, .DivisionByZero b
  | .RemainderByZero a, .RemainderByZero b | .InvalidEnumConstruction a, .InvalidEnumConstruction b => operand tables a b
  | .ResumedAfterReturn _, .ResumedAfterReturn _ | .ResumedAfterPanic _, .ResumedAfterPanic _
  | .ResumedAfterDrop _, .ResumedAfterDrop _ | .NullPointerDereference, .NullPointerDereference
  | .NullReferenceConstructed, .NullReferenceConstructed => pure ()
  | _, _ => throw "normalization changed assertion constructor"

private def asmOperand (tables : SyntaxTables) : InlineAsmOperandNode → InlineAsmOperandNode → Pairing Unit
  | .In _ a, .In _ b => operand tables a b
  | .Out _ _ a, .Out _ _ b => optionalPlace tables a b
  | .InOut _ _ a c, .InOut _ _ b d => do operand tables a b; optionalPlace tables c d
  | .Const a, .Const b | .SymFn a, .SymFn b => constant tables a b
  | .SymStatic _, .SymStatic _ | .Label _, .Label _ => pure ()
  | _, _ => throw "normalization changed assembly operand constructor"

private def terminator (tables : SyntaxTables) (a b : TerminatorId) : Pairing Unit :=
  once (·.terminators) (fun state terminators => {state with terminators}) a.index b.index do
    match (← entry tables.terminators a.index "terminator").kind,
        (← entry tables.terminators b.index "terminator").kind with
    | .SwitchInt a _, .SwitchInt b _ => operand tables a b
    | .Drop a .., .Drop b .. => place tables a b
    | .Call a c destA .., .Call b d destB .. =>
      operand tables a b
      array c d (fun a b => operand tables a.operand b.operand)
      place tables destA destB
    | .TailCall a c _, .TailCall b d _ =>
      operand tables a b
      array c d (fun a b => operand tables a.operand b.operand)
    | .Assert a _ c .., .Assert b _ d .. => operand tables a b; assertion tables c d
    | .Yield a _ c _, .Yield b _ d _ => operand tables a b; place tables c d
    | .InlineAsm a, .InlineAsm b => array a.operands b.operands (asmOperand tables)
    | .Goto .., .Goto .. | .UnwindResume, .UnwindResume | .UnwindTerminate _, .UnwindTerminate _
    | .Return, .Return | .Unreachable, .Unreachable | .CoroutineDrop, .CoroutineDrop
    | .FalseEdge .., .FalseEdge .. | .FalseUnwind .., .FalseUnwind .. => pure ()
    | _, _ => throw "normalization changed terminator constructor"

private def block (tables : SyntaxTables) (a b : BlockNodeId) : Pairing Unit :=
  once (·.blocks) (fun state blocks => {state with blocks}) a.index b.index do
    let a ← entry tables.blocks a.index "block"
    let b ← entry tables.blocks b.index "block"
    array a.statements b.statements (statement tables)
    terminator tables a.terminator b.terminator

def build (tables : SyntaxTables) (source normalized : BodyId) : Except String NormalizationData := do
  let source ← entry tables.bodies source.index "body"
  let normalized ← entry tables.bodies normalized.index "body"
  unless source.locals.size == normalized.locals.size do throw "normalization changed local count"
  let (_, state) ← (array source.basicBlocks normalized.basicBlocks (block tables)).run
    {types := Array.replicate tables.places.size none}
  return ⟨state.types,state.constants⟩

end Miri.Input.Reader.PlaceTypeReader
