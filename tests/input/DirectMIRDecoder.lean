import Miri.Input.DecodeMIR

open Miri.Input

private def context : DecodeMIR.Context := {
  typeCount := 1, allocationCount := 0, definitionCount := 1,
  typeConstantCount := 0, spanCount := 1, scalarSizes := #[some 1]
}

private def source := "{\"span\":0,\"scope\":0}"
private def literal (bits : String) :=
  "{\"kind\":\"Constant\",\"constant\":{\"type\":0,\"span\":0,\"user_type_annotation\":null," ++
  "\"constant\":{\"kind\":\"evaluated_const\"," ++
  "\"value\":{\"kind\":\"scalar\",\"bits_unsigned\":\"" ++ bits ++ "\"}}}}"
private def body (bits : String) (localId : Nat := 0) :=
  "{\"phase\":{\"kind\":\"built\"},\"instance_id\":0,\"arg_count\":0,\"spread_arg\":null," ++
  "\"locals\":[{\"local\":0,\"type\":0,\"source_info\":" ++ source ++ "}]," ++
  "\"basic_blocks\":[{\"block\":0,\"is_cleanup\":false,\"statements\":[{" ++
  "\"source_info\":" ++ source ++ ",\"kind\":{\"variant\":\"Assign\",\"place\":{\"local\":" ++ toString localId ++
  ",\"type\":0,\"projection\":[]},\"rvalue\":{\"kind\":\"Use\",\"retag\":{\"kind\":\"no\",\"performs_retag\":false},\"operand\":" ++ literal bits ++ "}}}]," ++
  "\"terminator\":{\"source_info\":" ++ source ++ ",\"kind\":{\"variant\":\"Return\"}}}]," ++
  "\"source_scopes\":[{\"scope\":0,\"span\":0,\"parent\":null,\"inlined\":null,\"inlined_parent_scope\":null}]," ++
  "\"source_def_id\":0,\"span\":0,\"preamble_def_span\":0,\"backtrace_spans\":[],\"required_consts\":[]}"

private def decode (text : String) := do
  DecodeMIR.resolveBody context (← JsonReader.run (DecodeMIR.parseBody "bodies[0]") text)

def main : IO Unit := do
  let .ok result := decode (body "255") | throw (IO.userError "valid scalar MIR did not decode")
  let some block := result.mir.basicBlocks[0]? | throw (IO.userError "missing block")
  let some stmt := block.statements[0]? | throw (IO.userError "missing statement")
  let .Assign _ (.Use (.Constant constant) _) := stmt.kind | throw (IO.userError "wrong MIR constructors")
  unless constant.value == .Val (.Scalar (.Int 255 1)) 0 do throw (IO.userError "wrong scalar byte width")
  unless (decode (body "256")).isOk == false do throw (IO.userError "oversized scalar accepted")
  unless (decode (body "0" 1)).isOk == false do throw (IO.userError "out-of-range place accepted")
  unless (decode ((body "0").replace "\"variant\":\"Return\"" "\"variant\":\"Goto\",\"target\":1,\"loop_hints\":[]")).isOk == false do
    throw (IO.userError "out-of-range block accepted")
  IO.println "direct MIR decoder: passed"
