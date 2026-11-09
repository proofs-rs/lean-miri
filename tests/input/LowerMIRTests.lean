import Miri.Input.Decoder
import Miri.Input.LowerMIR

open Miri Input

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def must (value : Except String α) : IO α :=
  match value with | .ok v => pure v | .error e => throw (IO.userError e)
private def replaceField (value : JsonReader.Slice) (name replacement : String) : Except String String := do
  let fields ← value.object
  pure ("{" ++ String.intercalate "," ((fields.toList.map fun (key,child) =>
    "\"" ++ key ++ "\":" ++ if key == name then replacement else child.text)) ++ "}")

def main (args : List String) : IO Unit := do
  let path ← match args with
    | path :: _ => pure path
    | [] => throw (IO.userError "usage: LowerMIRTests <selected add_one export>")
  let source ← IO.FS.readFile path
  let decoded ← must (decodeJson source)
  let input ← match decoded.document.bodies.find? (fun b => b.defPath.endsWith "add_one") with
    | some b => pure b.toBodyCore
    | none => throw (IO.userError "missing add_one fixture")
  let lowered ← must (lowerBody (LowerContext.ofDocument decoded.document) input)
  check (lowered.body == input.mir) "prepared body differs from directly decoded MIR"
  check (!lowered.spans.isEmpty) "actual source spans were not retained"
  check (lowered.body.basicBlocks.any fun b => match b.terminator.kind with
    | .Assert _ _ (.Overflow .Add _ _) _ .Continue => true | _ => false)
    "add_one checked-overflow terminator did not decode"
  check (lowered.body.basicBlocks.any fun b => b.statements.any fun s => match s.kind with
    | .Assign _ (.BinaryOp .AddWithOverflow _ _) => true | _ => false)
    "add_one arithmetic did not decode"
  let root ← must (JsonReader.parse source)
  let bodies ← must ((← must (root.field "bodies")).array)
  let some raw := bodies.find? (fun body => ((body.field "def_path").bind (·.string)).toOption == some input.defPath)
    | throw (IO.userError "missing body source")
  let document := decoded.document
  let ctx : DecodeMIR.Context := {
    typeCount := document.types.size, allocationCount := document.allocations.size,
    definitionCount := document.definitions.size, typeConstantCount := document.typeConstants.size,
    spanCount := document.spans.size, scalarSizes := document.types.map fun ty =>
      (document.layouts[ty.layoutId]?).bind (·.sizeBytes), threadLocal := DecoderValues.parseThreadLocal }
  check ((DecodeMIR.decodeBody {ctx with typeCount := 0} raw input.sourcePath).isOk == false) "unresolved type accepted"
  check ((DecodeMIR.decodeBody {ctx with scalarSizes := #[]} raw input.sourcePath).isOk == false) "missing scalar width accepted"
  let decodeMutation (name value : String) := do
    DecodeMIR.decodeBody ctx (← JsonReader.parse (← replaceField raw name value)) input.sourcePath
  check ((decodeMutation "phase" "{\"kind\":\"unknown\"}").isOk == false) "unknown phase accepted"
  check ((decodeMutation "source_scopes" "null").isOk == false) "missing source scopes accepted"
  check ((decodeMutation "spread_arg" (toString (input.mir.locals.size + 1))).isOk == false) "invalid spread argument accepted"
  IO.println "add_one direct MIR and malformed metadata checks passed"
