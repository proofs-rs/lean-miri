import Miri.Input.Reader.ExternStatics

open Lean Miri.Input Miri.Input.Reader

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def supported (value : Json) : Json := Json.mkObj [("status",toJson "supported"),("value",value)]
private def reference (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref",toJson id)]
private def definition : Json := Json.mkObj [("crate",toJson (2 : Nat)),("index",toJson (8 : Nat))]
private def declaration (freeze mutable : Bool) : Json := Json.mkObj [
  ("definition",reference 0),("status",toJson "supported"),("typing_env",toJson "fully_monomorphized"),
  ("type",Json.mkObj [("type_id",toJson (0 : Nat))]),
  ("layout",Json.mkObj [("size_bytes",toJson (4 : Nat)),("abi_align_bytes",toJson (4 : Nat))]),
  ("decl_is_mut",toJson mutable),("definition_mutability",toJson "immutable"),("type_is_freeze",toJson freeze),
  ("symbol",toJson "VALUE"),("import_linkage",Json.mkObj [("kind",toJson "none")])]

private def read (decl : Json) : IO (ExternStaticsData × MIRReader.State) := do
  let target := supported (Json.mkObj [("os",toJson "linux"),("env",toJson "gnu"),
    ("binary_format",toJson "elf"),("families",Json.arr #[toJson "unix"])])
  let source := supported (Json.mkObj [("typing_env",toJson "fully_monomorphized"),
    ("declarations",Json.arr #[reference 1]),("selected_exported",Json.arr #[])])
  let root := Json.mkObj [
    ("shared_payloads",Json.mkObj [("schema_version",toJson (2 : Nat)),("nodes",Json.arr #[definition,decl,target,source])]),
    ("compiler_runtime_queries",Json.mkObj [("foreign_symbols",Json.mkObj [("target",reference 2),("extern_statics",reference 3)])])]
  let catalog ← must (Catalog.parse root)
  let (result,state) ← must ((ExternStaticReader.read catalog 1 0).run (MIRReader.initial catalog.nodes.size {}))
  return (← must result,state)

def main : IO Unit := do
  let (data,state) ← read (declaration true false)
  let some row := data.declarations[0]? | throw (IO.userError "extern declaration absent")
  unless row.definition == 0 && row.symbol == "VALUE" && row.size.bytes == 4 &&
      row.result.isOk && !row.mutable && state.compiler.definitions == #[⟨2,8⟩] do
    throw (IO.userError "shared extern declaration changed")
  let target ← must data.targetFacts
  unless target.os == "linux" && target.families == #["unix"] do
    throw (IO.userError "shared target facts changed")
  let (data,state) ← read (declaration false false)
  let some row := data.declarations[0]? | throw (IO.userError "failed declaration absent")
  unless row.result.toOption.isNone && state.compiler.definitions == #[⟨2,8⟩] do
    throw (IO.userError "mutability mismatch failure or identity was lost")
