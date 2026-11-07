import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata
open Lean Miri Miri.Input
private def must (result : Except String A) : IO A :=
  match result with | .ok value => pure value | .error e => throw (IO.userError e)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
private def replace (j : Json) (key : String) (value : Json) : Except String Json :=
  match j with
  | .obj fields => .ok (Json.mkObj ((key, value) :: fields.toList.filter (·.1 != key)))
  | _ => .error "expected object"
private def changeEnd (root : Json) (id : Nat) (last : Json) (nicheMode : Bool := false) : Except String Json := do
  let catalog ← Reader.Catalog.parse root
  let rows ← catalog.array (← catalog.field catalog.root "types" "$") "types"
  let mut selected := none
  for row in rows do
    if (← catalog.natural (← catalog.field row "type_id" "type") "type_id") == id then
      selected := some row
  let some row := selected | throw "source type missing"
  let layout ← catalog.field row "layout" "type"
  let range ← if nicheMode then
      catalog.field (← catalog.field layout "largest_niche" "layout") "valid_range" "niche"
    else do
      let backend ← catalog.field layout "backend_repr" "layout"
      catalog.field (← catalog.field backend "scalar" "backend") "valid_range" "scalar"
  let slot ← catalog.sharedId? range "valid_range"
  let some slot := slot | throw "fixture range must be a shared entry"
  let edited ← replace (← catalog.inspect range "valid_range") "end" last
  if bound : slot < catalog.nodes.size then
    let nodes := catalog.nodes.set slot edited bound
    let shared ← replace (← field root "shared_payloads") "nodes" (.arr nodes)
    replace root "shared_payloads" shared
  else throw "range table index invalid"
private def rangeOf (document : ImportDocument) (id : Nat) : Except String (Nat × Nat) := do
  let some ty := document.types.find? (·.id == id) | throw "source u128 type missing"
  let layout ← document.layoutTable.lookup ty.layoutId |>.mapError (fun id => s!"missing layout {id}")
  let some backend := layout.backendRepresentation | throw "scalar backend missing"
  let some scalar := backend.scalar | throw "scalar missing"
  let some range := scalar.validRange | throw "range missing"
  pure range

def main (args : List String) : IO Unit := do
  let path::_ := args | throw (IO.userError "missing exported JSON")
  let source ← IO.FS.readFile path
  let original ← must (Json.parse source)
  let catalog ← must (Reader.Catalog.parse original)
  let primitive ← must (catalog.field (← must (catalog.field catalog.root "compiler_runtime_primitives" "$")) "u128" "primitives")
  let id ← must (catalog.natural (← must (catalog.field primitive "type_id" "u128")) "type_id")
  let decoded ← must (decodeJson source)
  let range ← must (rangeOf decoded.document id)
  check (range == (0,2^128-1)) "actual compiler u128 range was clipped"
  let metadata ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let layout ← must ((metadata.lookup id).mapError toString)
  match layout.layout.backendRepr with
  | .Scalar (.Initialized (value := .Int .I128 false) (validRange := range)) =>
    check (range.start.toNat == 0 && range.end.toNat == 2^128-1) "runtime u128 range changed"
  | _ => throw (IO.userError "runtime u128 scalar shape changed")
  for value in [0,2^64,2^128-1] do
    for encoded in [Json.str (toString value), toJson value] do
      let edited ← must (changeEnd original id encoded)
      let decoded ← must (decodeJson edited.compress)
      check ((← must (rangeOf decoded.document id)).2 == value) "decimal/natural value changed"
  check (metadata.source.types.any fun ty =>
    (metadata.lookup ty.id).toOption.any fun value => value.layout.largestNiche.any fun niche =>
      niche.value == .Int .I128 false && niche.validRange.start.toNat == 1 &&
        niche.validRange.end.toNat == 2^128-1) "actual compiler u128 niche range changed"
  let some nicheType := decoded.document.types.find? (fun ty =>
      (decoded.document.layoutTable.lookup ty.layoutId).toOption.any fun layout =>
        layout.largestNiche.any (·.validRange.2 == 2^128-1))
    | throw (IO.userError "actual NonZeroU128 niche missing")
  let invalid : List Json := [Json.str "", .str "-1", .str "+1", .str "1_0", .str "0xFF", .str "1.0",
    .str (toString (2^128 : Nat)), toJson (2^128 : Nat), toJson (-1 : Int), .bool true, .null]
  for encoded in invalid do
    let edited ← must (changeEnd original id encoded)
    check (!(decodeJson edited.compress).isOk) s!"invalid u128 range accepted: {encoded.compress}"
    let edited ← must (changeEnd original nicheType.id encoded true)
    check (!(decodeJson edited.compress).isOk) s!"invalid niche endpoint accepted: {encoded.compress}"
  IO.println "actual u128 compiler/runtime range exact; 6 decimal/natural cases preserved and 11 malformed/overflow scalar and niche cases rejected"
