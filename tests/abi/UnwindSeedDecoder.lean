import Miri.Input.TableTail
open Miri.Input

private def abi (unwind : String) (extra : String := "") : String :=
  "{\"arguments\":[],\"return\":{\"type\":0,\"layout\":0,\"mode\":{\"kind\":\"Initial\"}}," ++
  "\"calling_convention\":{\"kind\":\"rust\"},\"fixed_count\":0,\"c_variadic\":false," ++
  "\"unwind_seed\":" ++ unwind ++ extra ++ "}"
private def seed := "{\"abi\":{\"kind\":\"c\",\"unwind\":true},\"definition\":null,\"panic_unwinds\":false,\"panic_in_drop_unwinds\":false}"
private def rejects (text : String) : IO Unit := do
  match JsonReader.run DecoderValues.decodeCompilerFunctionAbi text with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "malformed or eager unwind input accepted")

def main : IO Unit := do
  match JsonReader.run DecoderValues.decodeCompilerFunctionAbi (abi seed) with
  | .ok parsed => unless parsed.unwindSeed.canUnwind do
      throw (IO.userError "foreign C-unwind must remain permitted with panic=abort")
  | .error reason => throw (IO.userError reason)
  rejects (abi seed ",\"can_unwind\":true")
  rejects (abi "{\"abi\":{\"kind\":\"rust\"},\"definition\":null,\"panic_unwinds\":true}")
  rejects (abi "{\"abi\":{\"kind\":\"rust\"},\"definition\":{},\"panic_unwinds\":true,\"panic_in_drop_unwinds\":true}")
  rejects (abi "{\"abi\":{\"kind\":\"rust\"},\"definition\":null,\"panic_unwinds\":true,\"panic_in_drop_unwinds\":true,\"result\":true}")
  IO.println "Unwind seed decoder rejects missing dependencies, unknown results and eager fields."
