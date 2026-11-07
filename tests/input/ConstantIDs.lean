import MiriTests.Input.SharedPayloads
import Miri.Input.Reader.Constants
import Miri.Input.LowerMIR
import Miri.Input.RuntimeMetadata

open Lean Miri Miri.Input

private def must (value : Except ε α) [ToString ε] : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: ConstantIDs <export.json>")
  let source ← IO.FS.readFile path
  -- Independent source-shaped oracle only; production keeps the wire DAG.
  let resolved ← must (SharedPayloads.resolveGraph (← must (Json.parse source)))
  let catalog ← must (Reader.Catalog.parse (← must (Json.parse source)))
  let decoded ← must (decodeRuntimeJson source)
  let context := LowerContext.ofDocument decoded.document
  let ctx : Reader.ConstantReader.Context :=
    ⟨decoded.document.types.size, decoded.document.allocations.size, context.scalarSizes⟩
  let mut state := Reader.MIRReader.initial catalog.nodes.size ⟨#[], #[], #[]⟩
  let mut count := 0
  for (raw, index) in catalog.nodes.toList.zipIdx do
    unless (raw.getObjVal? "constant").isOk && (raw.getObjVal? "span").isOk &&
        (raw.getObjVal? "user_type_annotation").isOk && (raw.getObjVal? "type").isOk do continue
    let some oracle := resolved.nodes[index]? | throw (IO.userError "oracle absent")
    let (expected, tables) ← must (lowerCompilerConstOperand context state.compiler
      (← must (context.decodeCompilerValue oracle)))
    let reference := Json.mkObj [("$lean_miri_shared_ref", toJson index)]
    let (id, next) ← must ((Reader.ConstantReader.constant catalog ctx reference "constant").run state)
    unless id == index do throw (IO.userError "constant wire ID changed")
    let actual ← must (next.tables.constants.lookup id)
    let compiler := next.compiler
    unless actual.operand == expected && compiler.definitions == tables.definitions &&
        compiler.typeConstants == tables.typeConstants && compiler.spans == tables.spans do
      throw (IO.userError s!"constant semantics changed at shared ID {index}")
    let evaluation := do
      let ty ← (← oracle.getObjVal? "type").getObjValAs? Nat "type_id"
      let value ← (← oracle.getObjVal? "constant").getObjVal? "value"
      lowerCompilerConstValue context ty (← context.decodeCompilerValue value)
    match evaluation,actual.evaluation with
    | .ok expected,.ok actual => unless expected == actual do throw (IO.userError "constant evaluation changed")
    | .error _,.error _ => pure ()
    | _,_ => throw (IO.userError "constant evaluation availability changed")
    let (_, repeated) ← must ((Reader.ConstantReader.constant catalog ctx reference "constant").run next)
    unless repeated.compiler.spans == compiler.spans do
      throw (IO.userError "shared constant span constructed twice")
    state := repeated
    count := count + 1
  unless count > 0 do throw (IO.userError "fixture lacks constants")
  IO.println s!"constant IDs: PASS ({count} shared constants; exact semantic values and stable identities)"
