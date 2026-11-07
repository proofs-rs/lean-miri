import MiriTests.Input.SharedPayloads
import Miri.Input.Reader.Generics
import Miri.Input.LowerMIR
import Miri.Input.RuntimeMetadata

open Lean Miri Miri.Input

private def must (value : Except ε α) [ToString ε] : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: GenericIDs <export.json>")
  let source ← IO.FS.readFile path
  -- Independent source-shaped oracle only; production keeps the wire DAG.
  let resolved ← must (SharedPayloads.resolveGraph (← must (Json.parse source)))
  let catalog ← must (Reader.Catalog.parse (← must (Json.parse source)))
  let decoded ← must (decodeRuntimeJson source)
  let context := LowerContext.ofDocument decoded.document
  let mut state := Reader.MIRReader.initial catalog.nodes.size ⟨#[], #[], #[]⟩
  let mut count := 0
  for (raw, index) in catalog.nodes.toList.zipIdx do
    let .arr values := raw | continue
    if values.isEmpty then continue
    let .ok kinds := values.mapM (fun value => do
      catalog.string (← catalog.field value "kind" "argument") "argument") | continue
    unless kinds.all (fun kind => kind == "type" || kind == "lifetime" || kind == "const") do continue
    let some oracle := resolved.nodes[index]? | throw (IO.userError "oracle absent")
    let (expected, tables) ← must (lowerCompilerGenericArgs context state.compiler
      (← must (context.decodeCompilerValue oracle)))
    let reference := Json.mkObj [("$lean_miri_shared_ref", toJson index)]
    let (id, next) ← must ((Reader.GenericReader.arguments catalog decoded.document.types.size reference "arguments").run state)
    unless id == index do throw (IO.userError "generic argument wire ID changed")
    let actual ← must (next.arguments.lookup id)
    unless actual == expected && next.compiler.definitions == tables.definitions &&
        next.compiler.typeConstants == tables.typeConstants do
      throw (IO.userError s!"generic semantics changed at shared ID {index}")
    let (_, repeated) ← must ((Reader.GenericReader.arguments catalog decoded.document.types.size reference "arguments").run next)
    unless repeated.compiler.definitions == tables.definitions &&
        repeated.compiler.typeConstants == tables.typeConstants do
      throw (IO.userError "shared generic arguments constructed twice")
    state := repeated
    count := count + 1
  unless count > 0 do throw (IO.userError "fixture lacks generic arguments")
  IO.println s!"generic IDs: PASS ({count} shared argument lists; exact semantic values and stable identities)"
