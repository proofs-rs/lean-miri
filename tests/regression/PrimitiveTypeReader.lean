import Miri.Input.Reader.PrimitiveTypes

open Lean Miri.Input Miri.Input.Reader

private def ensure (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

#eval do
  let reference := Json.mkObj [("$lean_miri_shared_ref", toJson (0 : Nat))]
  let supported := Json.mkObj [("status",toJson "supported"),("value",reference)]
  let unavailable := Json.mkObj [("status",toJson "unsupported"),("reason",toJson "producer obligation")]
  let catalog ← match Catalog.parse (Json.mkObj [
      ("shared_payloads",Json.mkObj [("schema_version",toJson (2 : Nat)),
        ("nodes",Json.arr #[Json.mkObj [("type_id",toJson (17 : Nat))]])]),
      ("compiler_runtime_primitives",Json.mkObj [("u8",reference),("ordering_enum",supported)]),
      ("compiler_named_types",Json.mkObj [("c_ulong",supported),("off_t",unavailable)]),
      ("compiler_windows_type_layouts",Json.mkObj [("crate_path",toJson #["std","sys","pal","windows","c"]),
        ("namespace",toJson "TypeNS"),("typing_env",toJson "fully_monomorphized"),
        ("entries",Json.mkObj [("FILETIME",supported),("missing_layout",unavailable)])]),
      ("compiler_libc_type_layouts",Json.mkObj [("crate_path",toJson #["libc"]),
        ("namespace",toJson "TypeNS"),("typing_env",toJson "fully_monomorphized"),
        ("entries",Json.mkObj [("pthread_t",supported)])])]) with
    | .ok value => pure value
    | .error reason => throw (IO.userError reason)
  let typed := catalog.readPrimitiveTypes
  ensure ((CompilerTypeCatalogs.lookup typed.primitives "u8").toOption == some 17) "shared primitive identity"
  ensure ((CompilerTypeCatalogs.lookup typed.primitiveQueries "ordering_enum").toOption == some 17) "shared supported primitive query"
  ensure ((CompilerTypeCatalogs.lookup typed.named "c_ulong").toOption == some 17) "shared named identity"
  ensure ((CompilerTypeCatalogs.lookup typed.libc "pthread_t").toOption == some 17) "libc canonical identity"
  ensure ((CompilerTypeCatalogs.lookup typed.windows "FILETIME").toOption == some 17) "Windows canonical identity"
  ensure (CompilerTypeCatalogs.lookup typed.windows "missing_layout").toOption.isNone "Windows unavailable query fails"
  let unsupported := match CompilerTypeCatalogs.lookup typed.named "off_t" with
    | .error reason => (reason.splitOn "producer obligation").length == 2
    | .ok _ => false
  ensure unsupported "unsupported reason preserved"
  ensure (CompilerTypeCatalogs.lookup typed.primitives "missing").toOption.isNone "missing query fails"
  let input ← match catalog.input with
    | .ok value => pure value
    | .error reason => throw (IO.userError reason)
  let .obj root := input | throw (IO.userError "expected root")
  for (catalogName,expected) in #[("compiler_libc_type_layouts","pthread_t"),
      ("compiler_windows_type_layouts","FILETIME")] do
    let .obj entries := (input.getObjVal? catalogName).toOption.getD .null
      | throw (IO.userError "expected type catalog")
    for (key,wrong) in #[("crate_path",toJson #["other"]),
        ("namespace",toJson "ValueNS"),("typing_env",toJson "post_analysis")] do
      let badEntries := Json.mkObj (entries.toList.map fun (name,value) =>
        (name,if name == key then wrong else value))
      let badInput := Json.mkObj (root.toList.map fun (name,value) =>
        (name,if name == catalogName then badEntries else value))
      let bad ← match Catalog.parse badInput with
        | .ok value => pure value
        | .error reason => throw (IO.userError reason)
      let values := bad.readPrimitiveTypes
      let table := if catalogName == "compiler_libc_type_layouts" then values.libc else values.windows
      ensure (CompilerTypeCatalogs.lookup table expected).toOption.isNone
        s!"invalid {catalogName} {key} rejected"
      ensure ((CompilerTypeCatalogs.lookup values.primitives "u8").toOption == some 17)
        "unrelated malformed catalog preserves primitive query"
  IO.println "typed primitive reader PASS"
