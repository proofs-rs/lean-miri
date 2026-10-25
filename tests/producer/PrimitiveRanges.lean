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
private def changeEnd (root : Json) (id : Nat) (last : Json) : Except String Json := do
  let types ← (← field root "types").getArr?
  let types ← types.mapM fun ty => do
    if (← (← field ty "type_id").getNat?) != id then return ty
    let layout ← field ty "layout"
    let backend ← field layout "backend_repr"
    let scalar ← field backend "scalar"
    let range ← field scalar "valid_range"
    let range ← replace range "end" last
    let scalar ← replace scalar "valid_range" range
    let backend ← replace backend "scalar" scalar
    let layout ← replace layout "backend_repr" backend
    replace ty "layout" layout
  replace root "types" (.arr types)
private def rangeOf (document : ImportDocument) (id : Nat) : Except String (Nat × Nat) := do
  let some ty := document.types.find? (·.id == id) | throw "source u128 type missing"
  let some backend := ty.layout.backendRepresentation | throw "scalar backend missing"
  let some scalar := backend.scalar | throw "scalar missing"
  let some range := scalar.validRange | throw "range missing"
  pure range

def main (args : List String) : IO Unit := do
  let path::_ := args | throw (IO.userError "missing exported JSON")
  let original ← must (Json.parse (← IO.FS.readFile path))
  let primitive ← must (field (← must (field original "compiler_runtime_primitives")) "u128")
  let id ← must ((← must (field primitive "type_id")).getNat?)
  let decoded ← must (decodeJson original.compress)
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
      check ((← must (rangeOf decoded.document id)).2 == value) "decimal/legacy natural changed"
  check (metadata.layouts.any fun (_, entry) =>
    entry.toOption.any fun value => value.layout.largestNiche.any fun niche =>
      niche.value == .Int .I128 false && niche.validRange.start.toNat == 1 &&
        niche.validRange.end.toNat == 2^128-1) "actual compiler u128 niche range changed"
  let some nicheType := decoded.document.types.find? (fun ty =>
    match ty.layout.payload.getObjValAs? Json "largest_niche" with
    | .ok niche => match niche.getObjVal? "valid_range" with
      | .ok range => (range.getObjValAs? String "end").toOption == some (toString (2^128-1 : Nat))
      | _ => false
    | _ => false) | throw (IO.userError "actual NonZeroU128 niche missing")
  let invalid : List Json := [Json.str "", .str "-1", .str "+1", .str "1_0", .str "0xFF", .str "1.0",
    .str (toString (2^128 : Nat)), toJson (2^128 : Nat), toJson (-1 : Int), .bool true, .null]
  for encoded in invalid do
    let edited ← must (changeEnd original id encoded)
    check (!(decodeJson edited.compress).isOk) s!"invalid u128 range accepted: {encoded.compress}"
    let niche ← must (field nicheType.layout.payload "largest_niche")
    let range ← must (field niche "valid_range")
    let range ← must (replace range "end" encoded)
    let niche ← must (replace niche "valid_range" range)
    let payload ← must (replace nicheType.layout.payload "largest_niche" niche)
    check (!(RuntimeMetadata.layout metadata.target { nicheType.layout with payload }).isOk)
      s!"invalid raw niche endpoint accepted: {encoded.compress}"
  IO.println "actual u128 compiler/runtime range exact; 6 decimal/legacy cases preserved and 11 malformed/overflow scalar and niche cases rejected"
