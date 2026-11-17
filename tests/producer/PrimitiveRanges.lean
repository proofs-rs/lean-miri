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

-- Schema 15 carries pattern range bounds as type-constant valtrees; scalar
-- layout ranges themselves are calculated from the type, not serialized.
private def changeBound (root : Json) (id : Nat) (bits : Json) : Except String Json := do
  let constants ← (← field root "type_constants").getArr?
  let some constant := constants[id]? | throw "pattern bound constant missing"
  let value ← replace (← field constant "value") "bits_unsigned" bits
  let constant ← replace constant "value" value
  replace root "type_constants" (.arr (constants.set! id constant))

private def bound (document : ImportDocument) (id : Nat) : Except String Nat := do
  let some (.Value _ tree) := document.typeConstants[id]? | throw "pattern bound is not concrete"
  let some (.Leaf bits _) := tree.nodes[tree.root]? | throw "pattern bound is not scalar"
  pure bits

def main (args : List String) : IO Unit := do
  let path::_ := args | throw (IO.userError "missing exported JSON")
  let source ← IO.FS.readFile path
  let original ← must (Json.parse source)
  let primitive ← must (field (← must (field original "compiler_runtime_primitives")) "u128")
  let id ← must primitive.getNat?
  let decoded ← must (decodeJson source)
  let metadata ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let layout ← must ((metadata.lookup id).mapError toString)
  match layout.layout.backendRepr with
  | .Scalar (.Initialized (value := .Int .I128 false) (validRange := range)) =>
    check (range.start.toNat == 0 && range.end.toNat == 2^128-1) "runtime u128 range changed"
  | _ => throw (IO.userError "runtime u128 scalar shape changed")
  check (metadata.source.types.any fun node =>
    (metadata.lookup node.id).toOption.any fun value => value.layout.largestNiche.any fun niche =>
      niche.value == .Int .I128 false && niche.validRange.start.toNat == 1 &&
        niche.validRange.end.toNat == 2^128-1) "actual compiler u128 niche range changed"
  let some pattern := decoded.document.types.find? (fun node => match node.shape with
      | .patternType base (.range _ _) => base == id
      | _ => false) | throw (IO.userError "actual u128 pattern range missing")
  let .patternType _ (.range start finish) := pattern.shape
    | throw (IO.userError "actual u128 pattern range changed")
  check ((← must (bound decoded.document start)) == 1 &&
    (← must (bound decoded.document finish)) == 2^128-1) "actual pattern bounds changed"
  for value in [0,2^64,2^128-1] do
    let edited ← must (changeBound original finish (Json.str (toString value)))
    let decoded ← must (decodeJson edited.compress)
    check ((← must (bound decoded.document finish)) == value) "decimal natural changed"
    let numeric ← must (changeBound original finish (toJson value))
    check (!(decodeJson numeric.compress).isOk) "numeric valtree bits accepted instead of decimal text"
  let invalid : List Json := [Json.str "", .str "-1", .str "+1", .str "1_0", .str "0xFF", .str "1.0",
    .str (toString (2^128 : Nat)), toJson (2^128 : Nat), toJson (-1 : Int), .bool true, .null]
  for id in [start, finish] do
    for encoded in invalid do
      let edited ← must (changeBound original id encoded)
      check (!(decodeJson edited.compress).isOk) s!"invalid pattern endpoint accepted: {encoded.compress}"
  IO.println "actual u128 runtime range and niche exact; pattern bounds preserve decimal values and reject malformed inputs"
