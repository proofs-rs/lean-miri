import Miri.Input.MIRLeaves

open Miri.Input

def main : IO Unit := do
  let valid := "{\"kind\":\"source_instance\",\"instance_id\":3,\"function_type\":5}"
  let .ok evidence := JsonReader.run DecodeMIR.callEvidence valid
    | throw (IO.userError "raw source instance call evidence was rejected")
  unless evidence.kind == .direct && evidence.instanceId == some 3 &&
      evidence.functionType == some 5 && evidence.dispatchSlot.isNone &&
      evidence.abi == .sourceSignature do
    throw (IO.userError "raw instance evidence changed complete identity or ABI demand")
  for invalid in [
      "{\"kind\":\"source_instance\",\"instance_id\":3,\"function_type\":5,\"fn_abi\":0}",
      "{\"kind\":\"source_instance\",\"instance_id\":3,\"function_type\":5,\"dispatch_slot\":0}",
      "{\"kind\":\"source_instance\",\"function_type\":5}",
      "{\"kind\":\"source_instance\",\"instance_id\":null,\"function_type\":5}",
      "{\"kind\":\"source_instance\",\"instance_id\":3}"] do
    if (JsonReader.run DecodeMIR.callEvidence invalid).isOk then
      throw (IO.userError "raw instance evidence accepted absent identity or mixed result fields")
  IO.println "PASS exact raw instance call evidence; missing/mixed identity and physical ABI fields reject"
