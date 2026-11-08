import Miri.Input.CompilerCastQueryRecord

open Lean Miri.Input.CompilerCastQueryRecord

private def record (fields : List (String × Json)) : Json :=
  Json.mkObj (("typing_env", .str "fully_monomorphized") :: fields)

def main : IO Unit := do
  let resolved := record [("resolution_kind", .str "instance"), ("instance_id", toJson (7 : Nat)),
    ("instance_kind", Json.mkObj [("kind", .str "item")]),
    ("generic_args", .arr #[])]
  unless (functionResult resolved).toOption == some (some resolved) do
    throw (IO.userError "direct resolved instance was not preserved")
  let direct := record [("instance_id", toJson (7 : Nat))]
  unless (functionResult direct).toOption == some (some direct) do
    throw (IO.userError "direct positive snapshot now requires a redundant tag")
  unless (functionResult (record [("resolution_kind", .str "none")])).toOption == some none do
    throw (IO.userError "genuine absent compiler target was not preserved")
  for malformed in [record [], record [("resolution_kind", .str "instance"), ("instance_id", .str "7")],
      record [("resolution_kind", .str "none"), ("instance_id", toJson (7 : Nat))],
      record [("resolution_kind", .str "future")],
      Json.mkObj [("instance_id", .null)],
      record [("value", resolved)]] do
    unless !(functionResult malformed).isOk do
      throw (IO.userError "missing, malformed or legacy instance identity accepted")
  for direct in [resolved,
      record [("source_tail", Json.mkObj [("type_id", toJson (1 : Nat))]),
        ("target_tail", Json.mkObj [("type_id", toJson (2 : Nat))])],
      record [("type_id", toJson (3 : Nat))]] do
    unless (payload direct).toOption == some direct do
      throw (IO.userError "direct cast result incorrectly requires value envelope")
  unless !(payload (Json.mkObj [("typing_env", .str "generic")])).isOk do
    throw (IO.userError "incorrect typing environment accepted")
  IO.println "CastQueryRecordChecks2026: direct casts and optional targets preserved"
