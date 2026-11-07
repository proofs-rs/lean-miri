import Miri.Input.Reader.Statements
import Miri.Input.RuntimeMetadata
import Miri.Input.LowerMIR

open Lean Miri Miri.Input

private def must (value : Except ε α) [ToString ε] : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: StatementIDs <export.json>")
  let source ← IO.FS.readFile path
  let catalog ← must (Reader.Catalog.parse (← must (Json.parse source)))
  let decoded ← must (decodeRuntimeJson source)
  let context := LowerContext.ofDocument decoded.document
  let ctx : Reader.ConstantReader.Context :=
    ⟨decoded.document.types.size, decoded.document.allocations.size, context.scalarSizes⟩
  let mut state := Reader.MIRReader.initial catalog.nodes.size ⟨#[], #[], #[]⟩
  let mut count := 0
  let mut assignments := 0
  for (raw, index) in catalog.nodes.toList.zipIdx do
    unless (raw.getObjVal? "source_info").isOk do continue
    let .ok kind := catalog.field raw "kind" "statement" | continue
    let .ok variant := catalog.string (← must (catalog.field kind "variant" "statement")) "statement" | continue
    unless #["Assign", "StorageLive", "StorageDead", "PlaceMention", "SetDiscriminant", "ConstEvalCounter",
      "Nop", "FakeRead", "AscribeUserType", "Coverage", "Intrinsic", "BackwardIncompatibleDropHint"].contains variant do continue
    let reference := Json.mkObj [("$lean_miri_shared_ref", toJson index)]
    let (id, next) ← must ((Reader.StatementReader.statement catalog ctx reference "statement").run state)
    unless id.index == index do throw (IO.userError "statement wire ID changed")
    let value ← must (next.tables.statements.lookup id.index)
    let sourceInfo ← must (catalog.field raw "source_info" "statement")
    let expected ← must (catalog.decodeSourceSpan (← must (catalog.field sourceInfo "span" "statement")) "statement")
    let some span := next.compiler.spans[value.sourceInfo.span.id]? | throw (IO.userError "span ID absent")
    unless span == expected do throw (IO.userError "source span changed")
    if let .Assign place value := value.kind then
      let _ ← must (next.tables.places.lookup place.index)
      let _ ← must (next.tables.rvalues.lookup value.index)
      assignments := assignments + 1
    let (_, repeated) ← must ((Reader.StatementReader.statement catalog ctx reference "statement").run next)
    unless repeated.tables == next.tables && repeated.compiler.spans == next.compiler.spans do
      throw (IO.userError "shared statement reconstructed")
    state := repeated
    count := count + 1
  unless assignments > 0 do throw (IO.userError "fixture lacks assignments")
  IO.println s!"statement IDs: PASS ({count} statements; {assignments} assignments; source spans and checked child IDs)"
