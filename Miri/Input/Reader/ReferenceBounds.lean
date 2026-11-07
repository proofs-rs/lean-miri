import Miri.Input.Reader.Bodies

namespace Miri.Input.Reader.ReferenceBounds
open Miri.MIR

private structure Bound where
  locals : Nat := 0
  blocks : Nat := 0
  scopes : Nat := 0

private def Bound.join (a b : Bound) : Bound :=
  ⟨max a.locals b.locals, max a.blocks b.blocks, max a.scopes b.scopes⟩

private structure Cache where
  operands : SharedTable Bound
  rvalues : SharedTable Bound
  statements : SharedTable Bound
  terminators : SharedTable Bound
  blocks : SharedTable Bound
private abbrev Check := StateT Cache (Except String)

private def entry (table : SharedTable α) (id : Nat) (kind : String) : Except String α :=
  (table.lookup id).mapError (fun id => s!"invalid MIR {kind} ID {id}")

private def cached (getTable : Cache → SharedTable Bound)
    (putTable : Cache → SharedTable Bound → Cache) (id : Nat) (compute : Check Bound) : Check Bound := do
  let state ← get
  let some slot := (getTable state)[id]? | throw s!"reference-bound slot absent for ID {id}"
  if let some value := slot then return value
  let value ← compute
  let state ← get
  let table := getTable state
  if bound : id < table.size then set (putTable state (table.set id (some value) bound))
  else throw s!"reference-bound slot absent for ID {id}"
  return value

private def place (source : MIRReader.State) (id : PlaceId) : Except String Bound := do
  let _ ← entry source.tables.places id.index "place"
  return {locals := ← entry source.placeLocals id.index "place local bound"}

private def operand (source : MIRReader.State) (id : OperandId) : Check Bound :=
  cached (·.operands) (fun state operands => {state with operands}) id.index do
    match ← entry source.tables.operands id.index "operand" with
    | .Copy id | .Move id => place source id
    | .Constant id => let _ ← entry source.tables.constants id.index "constant"; return {}
    | .RuntimeChecks _ => return {}

private def operands (source : MIRReader.State) (ids : Array OperandId) : Check Bound := do
  let mut result := {}
  for id in ids do result := result.join (← operand source id)
  return result

private def rvalue (source : MIRReader.State) (id : RvalueId) : Check Bound :=
  cached (·.rvalues) (fun state rvalues => {state with rvalues}) id.index do
    match ← entry source.tables.rvalues id.index "rvalue" with
    | .Use id _ | .Repeat id _ | .Cast _ id _ | .UnaryOp _ id | .WrapUnsafeBinder id _ => operand source id
    | .Ref _ _ id | .RawPtr _ id | .Discriminant id | .CopyForDeref id | .Reborrow _ _ id => place source id
    | .BinaryOp _ left right => return (← operand source left).join (← operand source right)
    | .Aggregate _ ids => operands source (← entry source.tables.operandLists ids.index "operand list")
    | .ThreadLocalRef _ => return {}

private def intrinsic (source : MIRReader.State) : IntrinsicNode → Check Bound
  | .Assume id => operand source id
  | .CopyNonOverlapping args => operands source #[args.source, args.destination, args.count]

private def statement (source : MIRReader.State) (id : StatementId) : Check Bound :=
  cached (·.statements) (fun state statements => {state with statements}) id.index do
    let node ← entry source.tables.statements id.index "statement"
    let bound ← (show Check Bound from do
      match node.kind with
      | .Assign dest value => return (← place source dest).join (← rvalue source value)
      | .FakeRead _ id | .SetDiscriminant id _ | .PlaceMention id | .AscribeUserType id _ _
      | .BackwardIncompatibleDropHint id _ => place source id
      | .StorageLive id | .StorageDead id => return {locals := id + 1}
      | .Intrinsic value => intrinsic source value
      | .Coverage _ | .ConstEvalCounter | .Nop => return {})
    return bound.join {scopes := node.sourceInfo.scope + 1}

private def unwind : UnwindAction → Bound
  | .Cleanup id => {blocks := id + 1}
  | _ => {}

private def assertion (source : MIRReader.State) : AssertNode → Check Bound
  | .BoundsCheck a b | .Overflow _ a b | .MisalignedPointerDereference a b => operands source #[a,b]
  | .OverflowNeg a | .DivisionByZero a | .RemainderByZero a | .InvalidEnumConstruction a => operand source a
  | .ResumedAfterReturn _ | .ResumedAfterPanic _ | .ResumedAfterDrop _
  | .NullPointerDereference | .NullReferenceConstructed => pure {}

private def optionalPlace (source : MIRReader.State) : Option PlaceId → Except String Bound
  | none => pure {}
  | some id => place source id

private def asmOperand (source : MIRReader.State) : InlineAsmOperandNode → Check Bound
  | .In _ id => operand source id
  | .Out _ _ id => optionalPlace source id
  | .InOut _ _ input output => do return (← operand source input).join (← optionalPlace source output)
  | .Const id | .SymFn id => do let _ ← entry source.tables.constants id.index "constant"; return {}
  | .SymStatic _ | .Label _ => pure {}

private def blockId (id : BasicBlockId) : Bound := {blocks := id + 1}
private def optionalBlock : Option BasicBlockId → Bound
  | none => {}
  | some id => blockId id

private def terminator (source : MIRReader.State) (id : TerminatorId) : Check Bound :=
  cached (·.terminators) (fun state terminators => {state with terminators}) id.index do
    let node ← entry source.tables.terminators id.index "terminator"
    let bound ← (show Check Bound from do
      match node.kind with
      | .Goto target _ => return blockId target
      | .SwitchInt id targets =>
        let mut bound ← operand source id
        bound := bound.join (blockId targets.otherwise)
        for .Case _ id in targets.cases do bound := bound.join (blockId id)
        return bound
      | .Drop id target action _ asyncDrop =>
        return (← place source id).join (blockId target) |>.join (unwind action) |>.join (optionalBlock asyncDrop)
      | .Call function args dest target action _ _ =>
        let bound ← operands source (args.map (·.operand))
        return bound.join (← operand source function) |>.join (← place source dest) |>.join (optionalBlock target) |>.join (unwind action)
      | .TailCall function args _ => return (← operand source function).join (← operands source (args.map (·.operand)))
      | .Assert condition _ message target action =>
        return (← operand source condition).join (← assertion source message) |>.join (blockId target) |>.join (unwind action)
      | .Yield id resume dest drop =>
        return (← operand source id).join (← place source dest) |>.join (blockId resume) |>.join (optionalBlock drop)
      | .FalseEdge real imaginary => return (blockId real).join (blockId imaginary)
      | .FalseUnwind target action => return (blockId target).join (unwind action)
      | .InlineAsm asm =>
        let mut bound := unwind asm.unwind
        for id in asm.targets do bound := bound.join (blockId id)
        for op in asm.operands do bound := bound.join (← asmOperand source op)
        return bound
      | .UnwindResume | .UnwindTerminate _ | .Return | .Unreachable | .CoroutineDrop => return {})
    return bound.join {scopes := node.sourceInfo.scope + 1}

private def block (source : MIRReader.State) (id : BlockNodeId) : Check Bound :=
  cached (·.blocks) (fun state blocks => {state with blocks}) id.index do
    let node ← entry source.tables.blocks id.index "block"
    let mut bound ← terminator source node.terminator
    for id in node.statements do bound := bound.join (← statement source id)
    return bound

-- A bound is reusable across bodies; validity is checked against each body's own scope.
def validate (source : MIRReader.State) (bodies : Array BodyId) : Except String Unit := do
  let cache : Cache := {
    operands := Array.replicate source.tables.operands.size none
    rvalues := Array.replicate source.tables.rvalues.size none
    statements := Array.replicate source.tables.statements.size none
    terminators := Array.replicate source.tables.terminators.size none
    blocks := Array.replicate source.tables.blocks.size none }
  let _ ← (show Check Unit from do
    for id in bodies do
      let node ← entry source.tables.bodies id.index "body"
      let mut bound : Bound := {}
      for id in node.basicBlocks do bound := bound.join (← block source id)
      unless bound.locals ≤ node.locals.size do throw s!"body {id.index}: local reference outside body"
      unless bound.blocks ≤ node.basicBlocks.size do throw s!"body {id.index}: block reference outside body"
      unless bound.scopes ≤ node.sourceScopeCount do throw s!"body {id.index}: source scope reference outside body").run cache
  return ()

end Miri.Input.Reader.ReferenceBounds
