import Miri.Input.Decoder
import Miri.Input.RuntimeArrayTypes
import Miri.Input.WorldTypeHash
open Lean Miri.Input
private def must {ε α} [ToString ε] : Except ε α → IO α
  | .ok value => pure value | .error error => throw (IO.userError (toString error))
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def load (path : String) : IO RuntimeArrayTypes.World := do
  let input ← must (decodeJson (← IO.FS.readFile path))
  let runtime ← must (RuntimeMetadata.ofDocument input.document)
  must ((RuntimeArrayTypes.create runtime).mapError reprStr)
private def oracleHash (rows : Array Json) (display : String) : IO Miri.ABI.U128 := do
  let some row := rows.find? (fun row => (row.getObjValAs? String "display").toOption == some display)
    | throw (IO.userError s!"independent hash oracle absent: {display}")
  let text ← must (row.getObjValAs? String "hash")
  let some value := text.toNat? | throw (IO.userError "invalid oracle hash")
  check (value < 2^128) "oracle hash exceeds u128"
  pure (BitVec.ofNat 128 value)

def main (args : List String) : IO Unit := do
  let [sourcePath,basePath,oraclePath] := args
    | throw (IO.userError "expected fresh structural export, primitive base and independent oracle")
  let source ← load sourcePath
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  let mut count := 0
  for node in source.arena.materialTypes do
    let some _ ← must (WorldTypeHash.sourceBytes source.arena 256 node.id) | continue
    if !(rows.any (fun row => (row.getObjValAs? String "display").toOption == some node.display)) then continue
    let expected ← oracleHash rows node.display
    let actual ← must (WorldTypeHash.query source.arena 256 node.id)
    check (actual == expected) s!"structural source hash differs: {node.display}"
    check (node.compilerFacts.bind (·.typeIdHash) |>.isNone)
      s!"covered type retained an eager hash: {node.display}"
    count := count + 1
  check (count >= 27) "structural hash differential domain incomplete"
  let base ← load basePath
  let primitive (display : String) : IO TypeId := do
    let some node := base.arena.materialTypes.find? (·.display == display)
      | throw (IO.userError s!"primitive base source missing: {display}")
    pure node.id
  let u32 ← primitive "u32"
  let boolean ← primitive "bool"
  let str ← primitive "str"
  let u16 ← primitive "u16"
  let construct : TypeArena.WorldM TypeId := do
    let pair ← TypeArena.World.internType (.tuple #[u32,boolean])
    let pointer ← TypeArena.World.internType (.rawPointer str .Mut)
    let slice ← TypeArena.World.internType (.slice u16)
    let slicePointer ← TypeArena.World.internType (.rawPointer slice .Not)
    TypeArena.World.internType (.tuple #[pair,pointer,slicePointer])
  let (novel,arena) ← must (construct.run base.arena)
  check (novel >= base.arena.materialTypes.size && arena.constructedTypes.size >= 4)
    "novel type was already in the material prefix"
  let world := {base with arena}
  let actual ← must (WorldTypeHash.query world.arena 256 novel)
  let expected ← oracleHash rows "((u32, bool), *mut str, *const [u16])"
  check (actual == expected) "novel constructed type hash differs from independent rustc"
  check (!(WorldTypeHash.query arena 0 novel).isOk) "type hash ignored source traversal exhaustion"
  check (!(WorldTypeHash.query world.arena 256 arena.typeCount).isOk) "missing runtime type hash invented"
  let candidates := base.arena.materialTypes.filter fun node =>
    (WorldTypeHash.sourceBytes base.arena 256 node.id).toOption == some none
  if let some residual := candidates[0]? then
    let types := base.arena.materialTypes.map fun node =>
      {node with compilerFacts := node.compilerFacts.map (fun facts => {facts with typeIdHash := none})}
    let missing ← must (TypeArena.World.ofMaterial types base.arena.materialConstants
      base.arena.definitions base.arena.materialPredicates base.arena.pointerBytes)
    check (!(WorldTypeHash.query missing 256 residual.id).isOk) "unsupported source type fabricated a missing hash"
  IO.println s!"PASS {count} independent rustc source type hashes without eager seeds; novel prefix-external type, missing identity and traversal controls"
