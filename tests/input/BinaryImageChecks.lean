import Miri.Input.JsonTraversalCache

open Lean Miri.Input

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def var (n : Nat) : ByteArray := Id.run do
  let mut remaining := n
  let mut bytes := ByteArray.empty
  for _ in [:10] do
    if remaining < 128 then return bytes.push remaining.toUInt8
    bytes := bytes.push ((remaining % 128).toUInt8 ||| 128)
    remaining := remaining / 128
  return bytes

private def text (value : String) : ByteArray := var value.utf8ByteSize ++ value.toUTF8
private def bytes (values : Array UInt8) : ByteArray := ⟨values⟩
private def row (tag : UInt8) (data : ByteArray := ByteArray.empty) : ByteArray :=
  (bytes #[tag]) ++ data
private def array (ids : Array Nat) : ByteArray :=
  row 5 (ids.foldl (fun out id => out ++ var id) (var ids.size))
private def object (pairs : Array (Nat × Nat)) : ByteArray :=
  row 6 (pairs.foldl (fun out (field,id) => out ++ var field ++ var id) (var pairs.size))
private def image (fields : Array String) (rows : Array ByteArray) (root : Nat) : ByteArray :=
  let header := fields.foldl (fun out value => out ++ text value)
    (BinaryImage.magic ++ var fields.size)
  rows.foldl (· ++ ·) (header ++ var rows.size) ++ var root

private def rejected (name : String) (input : ByteArray) (fragment : String := "") : IO Unit := do
  match JsonTraversalCache.resolveBinary input with
  | .ok _ => throw (IO.userError s!"{name}: malformed binary accepted")
  | .error error => check (error.contains fragment) s!"{name}: unexpected error: {error}"

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def main : IO Unit := do
  let fields := #["a", "n", "s", "z"]
  let rows := #[row 0, row 1, row 2, row 8 (var (2^63)), row 7 (var (2^64-1)),
    row 3 (text "-0.0"), row 4 (text "日本語\n"), array #[0,1,2,3,4,5,6],
    object #[(0,7),(1,4),(2,6),(3,7)]]
  let input := image fields rows 8
  let (decoded, node) ← must (JsonTraversalCache.resolveBinary input)
  let negativeZero ← must (Json.parse "-0.0")
  let reference := Json.mkObj [
    ("fields", toJson fields), ("root", toJson (8 : Nat)),
    ("schema", .str "lean-miri-prepared-image"), ("schema_version", toJson (1 : Nat)),
    ("nodes", .arr #[toJson (#[0] : Array Nat), toJson (#[1] : Array Nat),
      toJson (#[2] : Array Nat), .arr #[toJson (3 : Nat), toJson (-(2^63 : Int))],
      .arr #[toJson (3 : Nat), toJson (2^64-1 : Nat)], .arr #[toJson (3 : Nat), negativeZero],
      .arr #[toJson (4 : Nat), .str "日本語\n"],
      .arr #[toJson (5 : Nat), toJson (#[0,1,2,3,4,5,6] : Array Nat)],
      .arr #[toJson (6 : Nat), toJson (#[#[0,7],#[1,4],#[2,6],#[3,7]] : Array (Array Nat))]])]
  let (expected, expectedNode) ← must (JsonTraversalCache.resolve reference)
  check (decoded.root.compress == expected.root.compress &&
    decoded.nodes.map Json.compress == expected.nodes.map Json.compress)
    "binary leaves/ordered fields/aliases differ from independently constructed JSON rows"
  check (node.audit && expectedNode.audit && node.key.digest == expectedNode.key.digest)
    "locally computed hashes, child bindings or interest summaries differ"
  for stop in [:input.size] do rejected s!"prefix {stop}" (input.extract 0 stop)
  rejected "trailing" (input.push 0) "trailing"
  rejected "version" (input.set! 7 2) "magic"
  rejected "duplicate dictionary" (image #["a","a"] #[object #[]] 0) "duplicate"
  rejected "field range" (image #["a"] #[row 0,object #[(1,0)]] 1) "field ID"
  rejected "order" (image #["a","b"] #[row 0,object #[(1,0),(0,0)]] 1) "ordered"
  rejected "duplicate field" (image #["a"] #[row 0,object #[(0,0),(0,0)]] 1) "ordered"
  rejected "unused forward edge" (image #[] #[array #[0],object #[]] 1) "edge"
  rejected "reserved reference" (image #["$lean_miri_shared_ref"] #[row 0,object #[(0,0)]] 1) "reserved"
  rejected "reserved catalog" (image #["shared_payloads"] #[row 0,object #[(0,0)]] 1) "catalog"
  rejected "invalid number" (image #[] #[row 3 (text "true"),object #[]] 1) "number"
  rejected "negative zero integer" (image #[] #[row 8 (var 0),object #[]] 1) "negative"
  rejected "negative overflow" (image #[] #[row 8 (var (2^63+1)),object #[]] 1) "negative"
  rejected "unused invalid UTF-8" (image #[] #[row 4 (bytes #[1,255]),object #[]] 1) "UTF-8"
  rejected "unknown unused row" (image #[] #[row 9,object #[]] 1) "kind"
  rejected "empty table" (image #[] #[] 0) "root"
  rejected "scalar root" (image #[] #[row 0] 0) "object"
  rejected "noncanonical integer" (BinaryImage.magic ++ bytes #[128,0]) "noncanonical"
  rejected "u64 overflow" (BinaryImage.magic ++ bytes #[255,255,255,255,255,255,255,255,255,2]) "overflows"
  IO.println "binary image: scalar extremes, Unicode, aliases, hashes, every truncation and malformed/unused rows PASS"
