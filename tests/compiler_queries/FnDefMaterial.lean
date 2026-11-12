import Miri.Input.TableCore
import Miri.Input.GenericInstantiation

/-! Constructed controls distinguish FnDef argument binders from signature
binders. Fresh exported SourceCall comparisons supply the compiler oracle. -/
open Miri.Input Miri.Input.GenericSubstitution Miri.Input.GenericInstantiation

private def wire := r#"{"type_id":1,"display":"same","layout":0,"layout_query_input_type":null,"shape":{"kind":"function_definition","def_id":0,"def_path":"ignored","generic_args":[{"kind":"type","value":0}],"generic_args_bound_variables":[],"signature":{"inputs":[0],"output":0,"safety":{"kind":"safe"},"abi":{"kind":"rust","unwind":null},"c_variadic":false},"signature_bound_variables":[{"kind":"const"}]}}"#

private def reject (result : Except String α) (message : String) : Except String Unit :=
  match result with | .error _ => pure () | .ok _ => .error message

def main : IO Unit := do
  let checked : Except String Unit := do
    let function ← JsonReader.run (DecoderValues.parseTypeNode "$function") wire
    let scalar : TypeNode := {id := 0, display := "same", layoutId := 0, shape := .uint (.known .u32)}
    let context : Context := {
      types := #[scalar,function], definitions := #[{crateIndex := 7, index := 11}],
      constants := #[], pointerBytes := 8 }
    let expected : Term := .definition .type "function_definition" ⟨7,11⟩
      (.cons (.binder #[] (.node .aggregate "arguments" ""
        (.cons (.atom .type "uint" "u32") .nil))) .nil)
    unless (← ofType context 64 1) == expected do
      throw "FnDef identity was confused with its signature binder"
    unless (← resolveType context 64 expected) == 1 do throw "FnDef exact structural lookup failed"
    reject (JsonReader.run (DecoderValues.parseTypeNode "$function")
      (wire.replace "\"generic_args_bound_variables\":[]," "")) "missing mandatory FnDef args binder accepted"
    let boundWire := wire.replace "\"generic_args_bound_variables\":[]"
      "\"generic_args_bound_variables\":[{\"kind\":\"const\"}]"
    let bound ← JsonReader.run (DecoderValues.parseTypeNode "$function") boundWire
    let boundContext := {context with types := #[scalar,bound], denseTypes := none}
    reject (ofType boundContext 64 1) "unsupported nonempty FnDef argument binder accepted"
    reject (resolveType context 64 (.definition .type "function_definition" ⟨7,12⟩
      (.cons (.binder #[] (.node .aggregate "arguments" ""
        (.cons (.atom .type "uint" "u32") .nil))) .nil))) "unrelated physical FnDef accepted"
  match checked with
  | .ok () => IO.println "PASS strict FnDef source binder/identity and missing/unsupported controls"
  | .error error => throw (IO.userError error)
