import Miri.Input.CatalogDecoder

open Miri.Input

private def parse (fields : String) : Except String Catalog.CastQuery := do
  CatalogDecoder.castQuery (← JsonReader.parse
    ("{\"typing_env\":\"fully_monomorphized\",\"query_kind\":\"resolve_fn_ptr\",\"input_type\":1,\"args_no_bound_vars\":true," ++ fields ++ "}"))

def main : IO Unit := do
  unless (parse "\"resolution_kind\":\"instance\",\"instance_id\":7").toOption ==
      some (.resolveFnPtr 1 true (some 7)) do
    throw (IO.userError "direct resolved instance was not preserved")
  unless (parse "\"resolution_kind\":\"none\"").toOption == some (.resolveFnPtr 1 true none) do
    throw (IO.userError "genuine absent compiler target was not preserved")
  for fields in ["\"instance_id\":7", "\"resolution_kind\":\"instance\",\"instance_id\":\"7\"",
      "\"resolution_kind\":\"none\",\"instance_id\":7", "\"resolution_kind\":\"future\""] do
    unless !(parse fields).isOk do
      throw (IO.userError "missing or malformed instance identity accepted")
  IO.println "CastQueryRecordChecks2026: typed direct casts and optional targets preserved"
