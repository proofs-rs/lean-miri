import Miri.Input.Reader.Patterns

open Lean Miri Miri.Input Miri.Input.Reader

private def reference (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref",toJson id)]
private def record (kind : String) (fields : List (String × Json) := []) : Json :=
  Json.mkObj (("kind",toJson kind) :: ("status",toJson "supported") :: fields)
private def document (nodes : Array Json) : Json := Json.mkObj [
  ("shared_payloads",Json.mkObj [("schema_version",toJson (2 : Nat)),("nodes",.arr nodes)]),
  ("types",.arr #[Json.mkObj [("type_id",toJson (0 : Nat)),
    ("shape",Json.mkObj [("pattern",reference 6)])]])]
private def must (value : Except String A) : IO A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

def main : IO Unit := do
  let constant := record "error"
  let nodes := #[record "not_null",record "not_null",
    record "or" [("patterns",.arr #[reference 0,reference 1])],
    record "or" [("patterns",.arr #[reference 1,reference 0])],constant,
    record "range" [("start",reference 4),("end",reference 4)],
    record "range" [("start",constant),("end",reference 4)]]
  let catalog ← must (Catalog.parse (document nodes))
  let mut state := MIRReader.initial nodes.size {}
  let mut ids := #[]
  for id in [:nodes.size] do
    if id == 4 then continue
    let (id,next) ← must ((PatternReader.pattern catalog 1 (reference id) "pattern").run state)
    ids := ids.push id
    state := next
  unless ids == #[0,0,1,1,2,2] && state.patterns.size == 3 do
    throw (IO.userError "equal typed patterns received different canonical identities")
  unless state.compiler.typeConstants == #[MIR.TypeConst.Error] do
    throw (IO.userError "range endpoints were not interned once")
  let (types,next) ← must ((PatternReader.types catalog 1).run state)
  unless types == #[some 2] && next.patterns == state.patterns do
    throw (IO.userError "type pattern references were reconstructed")
  let badConstant := record "value" [("type",Json.mkObj [("type_id",toJson (1 : Nat))])]
  let changed ← if bound : 4 < nodes.size then pure (nodes.set 4 badConstant bound)
    else throw (IO.userError "constant node index absent")
  let changed ← must (Catalog.parse (document changed))
  unless !((PatternReader.pattern changed 1 (reference 5) "pattern").run (MIRReader.initial nodes.size {})).isOk do
    throw (IO.userError "out-of-bounds range endpoint type accepted")
  IO.println "pattern IDs: PASS (NotNull/Or/Range semantic canonicalization, shared endpoints, type bounds)"
