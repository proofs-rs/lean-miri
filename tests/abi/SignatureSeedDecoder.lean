import Miri.Input.TableTail
open Miri.Input
private def base := "{\"arguments\":[],\"return\":{\"type\":0,\"layout\":0,\"mode\":{\"kind\":\"Initial\"}},\"calling_convention\":{\"kind\":\"rust\"},\"c_variadic\":false,\"unwind_seed\":{\"abi\":{\"kind\":\"rust\",\"unwind\":null},\"definition\":null,\"panic_unwinds\":true,\"panic_in_drop_unwinds\":true}"
private def seed := "{\"signature\":{\"inputs\":[],\"output\":0,\"safety\":{\"kind\":\"safe\"},\"abi\":{\"kind\":\"rust\",\"unwind\":null},\"c_variadic\":false},\"extra_argument_types\":[],\"caller_location\":null}"
private def rejects (text : String) : IO Unit := do
  match JsonReader.run DecoderValues.decodeCompilerFunctionAbi text with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "ambiguous or absent ABI construction material accepted")
def main : IO Unit := do
  match JsonReader.run DecoderValues.decodeCompilerFunctionAbi
      (base ++ ",\"signature_seed\":" ++ seed ++ "}") with
  | .ok result => unless result.signatureSeed.isSome do
      throw (IO.userError "signature construction seed discarded")
  | .error reason => throw (IO.userError reason)
  rejects (base ++ "}")
  rejects (base ++ ",\"fixed_count\":0,\"signature_seed\":" ++ seed ++ "}")
  rejects (base ++ ",\"signature_seed\":{}" ++ "}")
  IO.println "Signature seed decoder requires one complete construction representation."
