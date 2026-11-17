import Miri.Input.SourceCastTargetsCodec

open Miri.Input

private def parse (fields : String) : Except String SourceCastTarget := do
  JsonReader.run SourceCastTargetsCodec.parse ("{" ++ fields ++ "}")

def main : IO Unit := do
  unless (parse "\"kind\":\"function_pointer\",\"input_type\":1,\"instance_id\":7").toOption ==
      some (.functionPointer 1 (some 7)) do
    throw (IO.userError "direct resolved instance was not preserved")
  unless (parse "\"kind\":\"function_pointer\",\"input_type\":1,\"instance_id\":null").toOption ==
      some (.functionPointer 1 none) do
    throw (IO.userError "genuine absent compiler target was not preserved")
  unless (parse "\"kind\":\"closure_once\",\"input_type\":1,\"instance_id\":7").toOption ==
      some (.closureOnce 1 7) do
    throw (IO.userError "closure target was not preserved")
  for fields in ["\"kind\":\"function_pointer\",\"input_type\":1",
      "\"kind\":\"function_pointer\",\"input_type\":1,\"instance_id\":\"7\"",
      "\"kind\":\"closure_once\",\"input_type\":1,\"instance_id\":null",
      "\"kind\":\"future\",\"input_type\":1,\"instance_id\":7"] do
    unless !(parse fields).isOk do
      throw (IO.userError "missing or malformed instance identity accepted")
  IO.println "CastQueryRecordChecks2026: source cast targets and optional identities preserved"
