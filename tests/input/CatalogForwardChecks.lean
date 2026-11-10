import Miri.Input.CatalogDecoder

open Miri.Input

private def context : DecodeMIR.Context := {
  typeCount := 43
  allocationCount := 1
  definitionCount := 1
  typeConstantCount := 0
  spanCount := 1
  scalarSizes := (Array.replicate 43 none).set! 42 (some 2)
}

private def expectWord (typeId : Nat) (value : DecodeMIR.DraftConstValue) : IO Unit := do
  match DecodeMIR.resolveConstValue context typeId value with
  | .ok (.Scalar (.Int 65535 2)) => pure ()
  | .ok _ => throw (IO.userError "catalog constant resolved with the wrong scalar width or value")
  | .error e => throw (IO.userError e)

private def unpack (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error e => throw (IO.userError e)

def main : IO Unit := do
  -- Layouts are unavailable during parsing: all three catalog forms carry a
  -- forward type reference and scalar bits larger than an 8-bit value.
  let named ← unpack <| JsonReader.run CatalogDecoder.namedConstant
    r#"{"query":{"evaluation":{"bits_unsigned":"65535","kind":"scalar"},"instance_id":0,"type":42},"path":["libc","WORD"],"name":"WORD","typing_env":"fully_monomorphized"}"#
  unless named.typeId == 42 && named.name == "WORD" do
    throw (IO.userError "named constant identity changed")
  expectWord named.typeId named.value
  let typeName ← unpack <| JsonReader.run CatalogDecoder.typeName
    r#"{"bits_unsigned":"65535","result_type":42,"kind":"scalar","typing_env":"fully_monomorphized","input_type":0}"#
  expectWord typeName.resultType typeName.value
  let caller ← unpack <| JsonReader.run CatalogDecoder.callerLocation
    r#"{"bits_unsigned":"65535","span":0,"kind":"scalar","result_type":42}"#
  expectWord caller.resultType caller.value
  for text in [
      r#"{"kind":"scalar","bits_unsigned":"1","result_type":-1,"span":0}"#,
      r#"{"kind":"scalar","bits_unsigned":"1","result_type":null,"span":0}"#,
      r#"{"kind":"scalar","bits_unsigned":"1","span":0}"#,
      r#"{"kind":"scalar","bits_unsigned":"1","result_type":42,"result_type":42,"span":0}"#,
      r#"{"kind":"scalar","bits_unsigned":"1","result_type":42,"span":0,"unknown":[1,]}"#] do
    if (JsonReader.run CatalogDecoder.callerLocation text).isOk then
      throw (IO.userError "malformed caller-location catalog row accepted")
  let tooWide ← unpack <| JsonReader.run CatalogDecoder.callerLocation
    r#"{"result_type":42,"span":0,"kind":"scalar","bits_unsigned":"65536"}"#
  if (DecodeMIR.resolveConstValue context tooWide.resultType tooWide.value).isOk then
    throw (IO.userError "oversized deferred catalog scalar accepted")
  let dangling ← unpack <| JsonReader.run CatalogDecoder.typeName
    r#"{"input_type":0,"result_type":43,"typing_env":"fully_monomorphized","kind":"zero_sized"}"#
  if (DecodeMIR.resolveConstValue context dangling.resultType dangling.value).isOk then
    throw (IO.userError "dangling catalog constant result type accepted")
  let pointer ← unpack <| JsonReader.run CatalogDecoder.callerLocation
    r#"{"result_type":42,"span":0,"kind":"pointer_scalar","allocation":1,"offset_bytes":0,"immutable":true,"shared_ref":false}"#
  if (DecodeMIR.resolveConstValue context pointer.resultType pointer.value).isOk then
    throw (IO.userError "dangling catalog allocation accepted")
  let cast := JsonReader.run CatalogDecoder.castQuery
    r#"{"typing_env":"fully_monomorphized","query_kind":"box_type","input_type":0,"type":42,"instance_id":0}"#
  if cast.isOk then throw (IO.userError "mixed cast query union payload accepted")
  IO.println "CatalogForwardChecks: reordered deferred constants, widths, references and malformed catalog rows checked"
