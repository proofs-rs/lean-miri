import MiriTests.Input.LegacyFixture

/-! Hypothetical fixture replay controls only. These do not establish the
original FnDef binder or any fresh compiler correspondence. -/
open Lean Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def hasBinder (source : String) : IO Bool := do
  let value ← must (Json.parse source)
  let types ← must ((← must (value.getObjVal? "types")).getArr?)
  let some node := types[1]? | throw (IO.userError "fixture FnDef missing")
  let shape ← must (node.getObjVal? "shape")
  pure (shape.getObjVal? "generic_args_bound_variables").isOk
private def fixture := r#"{"schema_version":11,"types":[{"shape":{"kind":"uint","unsigned_kind":"u32"}},{"shape":{"kind":"function_definition","generic_args":[{"kind":"type","value":0}]}}],"type_constants":[]}"#

def main : IO Unit := do
  unless (← hasBinder (← must (adaptLegacyFixture fixture))) do
    throw (IO.userError "bound-free historical replay lacks hypothetical binder")
  let bound := fixture.replace r#"{"kind":"uint","unsigned_kind":"u32"}"#
    r#"{"kind":"reference","pointee":0,"region":{"kind":"bound"}}"#
  if (← hasBinder (← must (adaptLegacyFixture bound))) then
    throw (IO.userError "indirect raw bound reference received an invented binder")
  let missing := fixture.replace r#""value":0"# r#""value":9"#
  if (← hasBinder (← must (adaptLegacyFixture missing))) then
    throw (IO.userError "missing type referent received an invented binder")
  let current := fixture.replace r#""schema_version":11"# r#""schema_version":13"#
  unless (← must (adaptLegacyFixture current)) == current do
    throw (IO.userError "current13 was rewritten by historical replay adapter")
  IO.println "PASS hypothetical FnDef replay, indirect bound/missing-ref rejection and strict current13 passthrough"
