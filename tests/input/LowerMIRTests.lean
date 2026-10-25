import Miri.Input.Decoder
import Miri.Input.LowerMIR

open Miri Input

-- Machine-checked constructor inventory; these counts concern syntax branches.
#guard ([RvalueVariant.use, .repeat, .ref, .threadLocalRef, .rawPtr, .cast,
  .binaryOp, .unaryOp, .discriminant, .aggregate, .copyForDeref,
  .wrapUnsafeBinder, .reborrow].filter rvalueLoweringBranch).length == 13
#guard ([StatementVariant.assign, .fakeRead, .setDiscriminant, .storageLive,
  .storageDead, .placeMention, .ascribeUserType, .coverage, .intrinsic,
  .constEvalCounter, .nop, .backwardIncompatibleDropHint].filter statementLoweringBranch).length == 12
#guard ([TerminatorVariant.goto, .switchInt, .unwindResume, .unwindTerminate,
  .return, .unreachable, .drop, .call, .tailCall, .assert, .yield,
  .coroutineDrop, .falseEdge, .falseUnwind, .inlineAsm].filter terminatorLoweringBranch).length == 15

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def must (value : Except String α) : IO α :=
  match value with | .ok v => pure v | .error e => throw (IO.userError e)

def main (args : List String) : IO Unit := do
  let path ← match args with
    | path :: _ => pure path
    | [] => throw (IO.userError "usage: LowerMIRTests <selected add_one export>")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let input ← match decoded.document.bodies.find? (fun b => b.defPath.endsWith "add_one") with
    | some b => pure b.toBodyCore
    | none => throw (IO.userError "missing add_one fixture")
  let ctx := LowerContext.ofTypes decoded.document.types
  let lowered ← must (lowerBody ctx input)
  check (lowered.body.argumentCount == input.argumentCount) "argument count lost"
  check (lowered.body.spreadArgument == input.spreadArgument) "spread argument lost"
  check (lowered.body.basicBlocks.size == input.blocks.size) "blocks lost"
  check (!lowered.spans.isEmpty) "actual source spans were not interned"
  check (lowered.spans.all fun s => !s.originalPayload.isEmpty) "source payload was discarded"
  check (lowered.body.basicBlocks.any fun b => match b.terminator.kind with
    | .Assert _ _ (.Overflow .Add _ _) _ .Continue => true | _ => false)
    "add_one checked-overflow terminator did not lower"
  check (lowered.body.basicBlocks.any fun b => b.statements.any fun s => match s.kind with
    | .Assign _ (.BinaryOp .AddWithOverflow _ _) => true | _ => false)
    "add_one arithmetic did not lower"
  check ((lowerBody (ctx.withTypeIds #[]) input).isOk == false) "unresolved metadata accepted"
  check ((lowerBody (ctx.withScalarSizes #[]) input).isOk == false) "missing scalar width accepted"
  check ((lowerBody ctx { input with phase := .scalar (.str "unknown") }).isOk == false) "unknown phase accepted"
  check ((lowerBody ctx { input with sourceScopes := none }).isOk == false) "missing source metadata accepted"
  check ((lowerBody ctx { input with spreadArgument := some input.locals.size }).isOk == false) "out-of-range spread argument accepted"
  let first ← match input.blocks[0]? with
    | some b => pure b
    | none => throw (IO.userError "empty fixture")
  let bad := { first with terminator := { first.terminator with value := .terminator (.unknown "future") .supported #[] } }
  check ((lowerBody ctx { input with blocks := input.blocks.set! 0 bad }).isOk == false) "unknown terminator accepted"
  let outOfRange := { first with terminator := { first.terminator with
    value := .terminator .falseEdge .supported #[("real_target", .blockRef input.blocks.size), ("imaginary_target", .blockRef 0)] } }
  check ((lowerBody ctx { input with blocks := input.blocks.set! 0 outOfRange }).isOk == false) "out-of-range CFG edge accepted"
  IO.println s!"add_one lowered: {lowered.body.basicBlocks.size} blocks, {lowered.spans.size} actual spans; negative metadata/phase/constructor checks passed"
