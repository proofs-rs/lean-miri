import Miri.Input.Reader.InlineAsm

namespace Miri.Input.Reader.TerminatorReader
open Lean Miri.MIR
abbrev Decode := MIRReader.Decode

private def assertion (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode AssertNode := do
  let field := fun key => catalog.field input key path
  let operand := fun key => do OperandReader.operand catalog ctx (← field key) path
  match ← catalog.string (← field "kind") path with
  | "Overflow" =>
    let some op := DecoderValues.binOpFromExportTag (← catalog.string (← catalog.field (← field "operator") "kind" path) path)
      | throw s!"{path}: unsupported assertion operator"
    return .Overflow op (← operand "left") (← operand "right")
  | "BoundsCheck" => return .BoundsCheck (← operand "length") (← operand "index")
  | "OverflowNeg" => return .OverflowNeg (← operand "operand")
  | "DivisionByZero" => return .DivisionByZero (← operand "operand")
  | "RemainderByZero" => return .RemainderByZero (← operand "operand")
  | "NullPointerDereference" => return .NullPointerDereference
  | "NullReferenceConstructed" => return .NullReferenceConstructed
  | "ResumedAfterReturn" => return .ResumedAfterReturn (← catalog.coroutine (← field "coroutine_kind") path)
  | "ResumedAfterPanic" => return .ResumedAfterPanic (← catalog.coroutine (← field "coroutine_kind") path)
  | "ResumedAfterDrop" => return .ResumedAfterDrop (← catalog.coroutine (← field "coroutine_kind") path)
  | "MisalignedPointerDereference" => return .MisalignedPointerDereference (← operand "required") (← operand "found")
  | "InvalidEnumConstruction" => return .InvalidEnumConstruction (← operand "operand")
  | kind => throw s!"{path}: unsupported assertion kind {kind}"

private def optionalBlock (catalog : Catalog) (input : Json) (path : String) : Except String (Option BasicBlockId) := do
  let value ← catalog.inspect input path
  if value == .null then return none
  return some (← catalog.natural value path)

private def spannedOperand (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode SpannedOperandNode := do
  return ⟨← ConstantReader.span catalog (← catalog.field input "span" path) path,
    ← OperandReader.operand catalog ctx (← catalog.field input "operand" path) path⟩

private def kind (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode TerminatorKindNode := do
  let field := fun key => catalog.field input key path
  let natural := fun key => do catalog.natural (← field key) path
  let operand := fun key => do OperandReader.operand catalog ctx (← field key) path
  let place := fun key => do OperandReader.place catalog ctx.typeCount (← field key) path
  let unwind := do catalog.unwind (← field "unwind") path
  let arguments : Decode (Array SpannedOperandNode) := do
    (← catalog.array (← field "args") path).mapIdxM fun index input =>
      spannedOperand catalog ctx input s!"{path}.args[{index}]"
  let span : Decode SpanRef := do ConstantReader.span catalog (← field "function_span") path
  unless (← catalog.string (← field "status") path) == "supported" do throw s!"{path}: unsupported terminator"
  match ← catalog.string (← field "variant") path with
  | "Return" => return .Return
  | "Unreachable" => return .Unreachable
  | "UnwindResume" => return .UnwindResume
  | "CoroutineDrop" => return .CoroutineDrop
  | "Assert" =>
    return .Assert (← operand "condition") (← catalog.boolean (← field "expected") path)
      (← assertion catalog ctx (← field "message") path) (← natural "target") (← unwind)
  | "FalseEdge" => return .FalseEdge (← natural "real_target") (← natural "imaginary_target")
  | "Goto" =>
    let hints ← (← catalog.array (← field "loop_hints") path).mapM fun input => catalog.loopHint input path
    return .Goto (← natural "target") hints
  | "SwitchInt" =>
    let targets ← (← catalog.array (← field "targets") path).mapM fun entry => do
      let value ← catalog.string (← catalog.field entry "value" path) path
      let some value := value.toNat? | throw s!"{path}: invalid switch value"
      return SwitchTarget.Case value (← catalog.natural (← catalog.field entry "target" path) path)
    return .SwitchInt (← operand "discriminant") ⟨targets, ← natural "otherwise"⟩
  | "UnwindTerminate" => return .UnwindTerminate (← catalog.unwindReason (← field "reason") path)
  | "Drop" =>
    return .Drop (← place "place") (← natural "target") (← unwind) (← catalog.boolean (← field "replace") path)
      (← optionalBlock catalog (← field "async_drop") path)
  | "Call" =>
    return .Call (← operand "function") (← arguments) (← place "destination")
      (← optionalBlock catalog (← field "target") path) (← unwind)
      (← catalog.callSource (← field "call_source") path) (← span)
  | "TailCall" => return .TailCall (← operand "function") (← arguments) (← span)
  | "Yield" =>
    return .Yield (← operand "value") (← natural "resume") (← place "resume_arg")
      (← optionalBlock catalog (← field "drop") path)
  | "FalseUnwind" => return .FalseUnwind (← natural "real_target") (← unwind)
  | "InlineAsm" => return .InlineAsm (← InlineAsmReader.read catalog ctx input path)
  | kind => throw s!"{path}: unsupported terminator variant {kind}"

def terminator (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode TerminatorId := do
  return ⟨← catalog.readCached (·.tables.terminators) (fun state terminators => {state with tables := {state.tables with terminators}})
    (fun input path => do
      let kind ← kind catalog ctx (← catalog.field input "kind" path) path
      return ⟨← StatementReader.sourceInfo catalog (← catalog.field input "source_info" path) path, kind⟩) input path⟩

end Miri.Input.Reader.TerminatorReader
