import Miri.Input.Reader.ThreadLocalQueries

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)
private def ref (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref",toJson id)]
private def info (foreign : Bool) : Json := Json.mkObj [
  ("status",toJson "supported"),("size_bytes",toJson (1 : Nat)),("align_bytes",toJson (1 : Nat)),
  ("mutability",toJson "mutable"),("is_static",toJson true),("is_foreign_item",toJson foreign),
  ("thread_local",toJson true),("nested",toJson false)]
private def memory (bytes : String) : Json := Json.mkObj [
  ("bytes_hex",toJson bytes),("size_bytes",toJson (1 : Nat)),("align_bytes",toJson (1 : Nat)),
  ("mutability",toJson "mutable"),("relocations",.arr #[]),
  ("initialization_ranges",.arr #[Json.mkObj [("state",toJson "initialized"),
    ("start_bytes",toJson (0 : Nat)),("end_bytes_exclusive",toJson (1 : Nat))]])]
private def source (declaration initializer : Json) : Json :=
  Json.mkObj [("global_info",declaration),("initializer",initializer)]

def main : IO Unit := do
  let nodes := #[info false,memory "00",
    Json.mkObj [("status",toJson "supported"),("allocation",ref 1)],source (ref 0) (ref 2)]
  let catalog ← must (Reader.Catalog.parse (Json.mkObj [
    ("shared_payloads",Json.mkObj [("schema_version",toJson (2 : Nat)),("nodes",.arr nodes)])]))
  let initial := Reader.MIRReader.initial nodes.size {definitions := #[⟨0,7⟩,⟨0,8⟩]}
  let (_,state) ← must ((Reader.ThreadLocalQueryReader.register catalog 0 (ref 3) "tls").run initial)
  let (_,state) ← must ((Reader.ThreadLocalQueryReader.register catalog 0 (ref 3) "tls").run state)
  let table := Reader.ThreadLocalQueryReader.finish state
  let actual ← must (← must (table.entries.lookup 0 |>.mapError toString))
  unless actual.sourceDefinition == ⟨0,7⟩ && actual.initializer.map (·.bytesHex) == some "00" &&
      (← must table.all).size == 1 do throw (IO.userError "shared TLS query or canonical identity changed")
  let failed := source (info false) (Json.mkObj [("status",toJson "unsupported")])
  let (_,state) ← must ((Reader.ThreadLocalQueryReader.register catalog 1 failed "other").run state)
  let table := Reader.ThreadLocalQueryReader.finish state
  unless (← must (table.entries.lookup 0 |>.mapError toString)).isOk &&
      !(← must (table.entries.lookup 1 |>.mapError toString)).isOk && !table.all.isOk do
    throw (IO.userError "unrelated TLS query was demanded or failed query was lost")
  let conflict := source (info false) (Json.mkObj [("status",toJson "supported"),("allocation",memory "ff")])
  let (_,state) ← must ((Reader.ThreadLocalQueryReader.register catalog 0 conflict "conflict").run state)
  let table := Reader.ThreadLocalQueryReader.finish state
  unless (← must (table.entries.lookup 0 |>.mapError toString)) == .error "conflicting compiler TLS query evidence" do
    throw (IO.userError "conflicting TLS initializer accepted")
  let foreign := source (info true) (Json.mkObj [("status",toJson "unsupported")])
  let (_,state) ← must ((Reader.ThreadLocalQueryReader.register catalog 0 foreign "foreign").run initial)
  let table := Reader.ThreadLocalQueryReader.finish state
  let actual ← must (← must (table.entries.lookup 0 |>.mapError toString))
  unless actual.info.foreignItem && actual.initializer.isNone do
    throw (IO.userError "foreign TLS initializer was synthesized")
  IO.println "thread-local typed tables: PASS"
