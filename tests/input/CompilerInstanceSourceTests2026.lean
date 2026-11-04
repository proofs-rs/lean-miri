import Miri.Input.CompilerInstance
import Miri.Input.Decoder

open Lean Miri.Input Miri.Interpreter

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error e => throw (IO.userError e)
private def set (j : Json) (key : String) (value : Json) : Json :=
  match j with
  | .obj fields => Json.mkObj ((key,value) :: fields.toList.filter (·.1 != key))
  | _ => Json.mkObj [(key,value)]
private def sameTables (a b : CompilerTables) : Bool :=
  a.spans == b.spans && a.definitions == b.definitions && a.typeConstants == b.typeConstants
private def compare (ctx : LowerContext) (tables : CompilerTables) (record : Json) : IO Unit := do
  match CompilerInstance.decode ctx tables record, CompilerInstance.decodeReference ctx tables record with
  | .ok (a,ta), .ok (b,tb) =>
    unless a == b && sameTables ta tb do throw (IO.userError "instance kind/args or appended table IDs changed")
  | .error a, .error b =>
    unless a == b do throw (IO.userError s!"first instance diagnostic changed: {a} / {b}")
  | _, _ => throw (IO.userError "instance decoder result class changed")

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected genuine compiler export")
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile path))
  let program ← must (lowerCoreProgram decoded.document)
  let ctx := LowerContext.ofDocument decoded.document
  let mut authentic := 0
  let mut hits := 0
  for raw in decoded.document.sharedNodes do
    if (raw.getObjVal? "instance_kind").isOk && (raw.getObjVal? "generic_args").isOk then
      compare ctx program.compilerTables raw
      if (ctx.compilerInstanceSourceMemo.bind (·.lookup raw)).isSome then hits := hits + 1
      authentic := authentic + 1
  unless authentic > 0 && hits > 0 do throw (IO.userError "fixture did not exercise checked instance reuse")
  let some ty := decoded.document.types[0]? | throw (IO.userError "missing type")
  let definition := Json.mkObj [("crate", toJson (99 : Nat)), ("index", toJson (101 : Nat))]
  let second := set definition "index" (toJson (102 : Nat))
  let typeRef := Json.mkObj [("type_id", toJson ty.id)]
  let base := Json.mkObj [("kind", .str "shim"), ("def_id",definition),
    ("call_once_def_id",definition), ("closure_def_id",second), ("track_caller",.bool true),
    ("receiver_by_ref",.bool true), ("function_type",typeRef), ("proxy_coroutine_type",typeRef),
    ("implementation_coroutine_type",typeRef), ("drop_type",typeRef), ("clone_type",typeRef),
    ("coroutine_type",typeRef), ("reason",.null), ("dispatch_slot",toJson (7 : Nat))]
  let mut kinds := #[]
  for tag in ["item","intrinsic","llvm_intrinsic","virtual"] do
    kinds := kinds.push (set base "kind" (.str tag))
  for tag in ["vtable","reify","fn_pointer","closure_once","construct_coroutine_in_closure",
      "thread_local","future_drop_poll","drop_glue","clone","fn_pointer_as_pointer",
      "fn_pointer_from_pointer","async_drop_glue_constructor","async_drop_glue"] do
    kinds := kinds.push (set base "shim_kind" (.str tag))
  for reason in ["function_pointer","vtable","invalid"] do
    kinds := kinds.push (set (set base "shim_kind" (.str "reify")) "reason" (.str reason))
  kinds := kinds.push (set (set base "shim_kind" (.str "drop_glue")) "drop_type" .null)
  kinds := kinds.push (set (set base "shim_kind" (.str "fn_pointer")) "function_type"
    (Json.mkObj [("type_id",toJson (100000000 : Nat))]))
  kinds := kinds.push (set (set base "kind" (.str "item")) "def_id" (.str "bad"))
  kinds := kinds.push (set base "kind" (.str "unknown"))
  let records := kinds.map fun kind => Json.mkObj [("instance_kind",kind),("generic_args",.arr #[])]
  let values := DecoderValues.prepareCompilerValueMemoUsing records DecoderValues.emptyDecodeMemo
  let memo := prepareCompilerInstanceSourceMemo records values
  let cached := { ctx with compilerInstanceSourceMemo := some memo }
  let changedContext := { LowerContext.ofTypes #[] with compilerInstanceSourceMemo := some memo }
  let tables : CompilerTables := ⟨#[], #[⟨98,100⟩], #[]⟩
  for record in records do
    compare cached tables record
    compare changedContext tables record
    compare cached tables (set record "generic_args" (.bool true))
  IO.println s!"typed compiler instance sources: {authentic} authentic rows ({hits} reused), {records.size} kind/error cases, changed contexts and sources PASS"
