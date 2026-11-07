import Miri.Input.Reader.StartupQueries

open Lean Miri.Input Miri.Input.Reader

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def reference (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref",toJson id)]
private def supported (value : Json) : Json := Json.mkObj [("status",toJson "supported"),("value",value)]
private def catalog (fields : List (String × Json)) (nodes : Array Json := #[]) : IO Catalog := do
  must (Catalog.parse (Json.mkObj (("shared_payloads",Json.mkObj [
    ("schema_version",toJson (2 : Nat)),("nodes",Json.arr nodes)]) :: fields)))

private def panicCase (settings : Json) (expected : Except String Bool) : IO Unit := do
  let source ← catalog [("producer",Json.mkObj [("input_settings",settings)])]
  unless StartupQueryReader.panicUnwinds source == expected do
    throw (IO.userError "source panic strategy result or error classification changed")

def main : IO Unit := do
  let definition := Json.mkObj [("crate",toJson (4 : Nat)),("index",toJson (9 : Nat))]
  let escape := supported (Json.mkObj [("definition",reference 0),("mir_available",toJson false)])
  let startup := Json.mkObj [("no_core",reference 1),("core_escape_default",reference 2)]
  let source ← catalog [("compiler_runtime_queries",Json.mkObj [("startup",reference 3)])]
    #[definition,supported (toJson true),escape,startup]
  let data ← must (StartupQueryReader.read source)
  unless data.noCore == .ok true && data.coreEscapeDefault == .ok (⟨4,9⟩,false) do
    throw (IO.userError "shared startup facts changed")
  let source ← catalog [("compiler_runtime_queries",Json.mkObj [("startup",reference 3)])]
    #[definition,Json.mkObj [("status",toJson "unsupported"),("reason",toJson "requires core")],escape,startup]
  let data ← must (StartupQueryReader.read source)
  unless data.noCore == .error "requires core" && data.coreEscapeDefault.isOk do
    throw (IO.userError "startup query failures were coupled")
  let settings (strategy : Json) := Json.mkObj [("status",toJson "supported"),("effective_panic_strategy",strategy)]
  panicCase (settings (toJson "unwind")) (.ok true)
  panicCase (settings (toJson "abort")) (.ok false)
  panicCase (settings (toJson "immediate-abort")) (.ok false)
  panicCase (settings (toJson "unknown")) (.error "unknown source compiler panic strategy: unknown")
  panicCase (settings (toJson (0 : Nat))) (.error "source compiler panic strategy is malformed")
  panicCase (Json.mkObj [("status",toJson "supported")]) (.error "source compiler panic strategy is missing")
  panicCase (Json.mkObj [("status",toJson "unsupported")]) (.error "source compiler settings are not supported")
  panicCase (Json.mkObj [("status",.null)]) (.error "source compiler settings status is malformed")
  panicCase (Json.mkObj []) (.error "source compiler settings status is missing")
  let source ← catalog []
  unless StartupQueryReader.panicUnwinds source == .error "source compiler panic strategy is missing" do
    throw (IO.userError "missing source producer error changed")
  let source ← catalog [("producer",reference 2)] #[toJson "supported",toJson "unwind",
    Json.mkObj [("input_settings",Json.mkObj [("status",reference 0),("effective_panic_strategy",reference 1)])]]
  unless StartupQueryReader.panicUnwinds source == .ok true do throw (IO.userError "shared panic strategy changed")
