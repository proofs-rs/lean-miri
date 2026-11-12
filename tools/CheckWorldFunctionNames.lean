import Miri.Input.WorldTypeName
import Miri.Input.WorldIntrinsicTypeName
import Miri.Input.Decoder
open Lean Miri.Input Miri.Input.TypeArena
private def must (value : Except String A) : IO A :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
private def headerName : DefinitionPath.HeaderSafety → String
  | .normalSafe => "normal_safe" | .normalUnsafe => "normal_unsafe" | .safeTargetFeatures => "safe_target_features"
def main (args : List String) : IO Unit := do
  let [source,oracle] := args | throw (IO.userError "expected fresh source oracle")
  let decoded ← must (decodeJson (← IO.FS.readFile source))
  let metadata ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let initial ← must (World.ofDocument decoded.document)
  let mut world := initial
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oracle))).getArr?)
  unless rows.size == 5 do throw (IO.userError "requires five function cases")
  for row in rows do
    let term ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "type")))
    let (id,next) ← must ((GenericInstantiationWorld.resolveType 512 term).run world)
    world := next
    unless id >= world.materialTypes.size do throw (IO.userError "function case was material seeded")
    let .constructed (.functionDefinition identity _ _) ← must (world.lookupType id)
      | throw (IO.userError "oracle type is not a novel FnDef")
    let definition ← must (world.definitionRef identity)
    let some source := world.definitions[definition]? | throw (IO.userError "source definition missing")
    let some header := source.rawPath.bind (·.functionHeaderSafety) | throw (IO.userError "raw header missing")
    let expectedHeader ← must ((← must (row.getObjVal? "raw_header_safety")).getStr?)
    unless headerName header == expectedHeader do throw (IO.userError "raw HIR header differs from pinned source")
    let (diagnostic,next) ← must ((WorldTypeName.query metadata 512 id).run world)
    world := next
    let expected ← must ((← must (row.getObjVal? "display")).getStr?)
    unless diagnostic == expected do throw (IO.userError s!"FnDef diagnostic differs from pinned rustc: {diagnostic} vs {expected}")
    let (intrinsic,next) ← must ((WorldIntrinsicTypeName.query metadata 512 id).run world)
    world := next
    let expected ← must ((← must (row.getObjVal? "intrinsic")).getStr?)
    unless intrinsic == expected do throw (IO.userError s!"FnDef intrinsic differs from pinned rustc: {intrinsic} vs {expected}")
  IO.println "PASS ten exact diagnostic/intrinsic strings and raw HIR headers across five novel FnDefs; allocation transport excluded"
