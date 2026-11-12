import NativeStdioProtocol

open Lean NativeStdioProtocol

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def rejected (args : List String) : Bool :=
  match splitArgs args with | .error _ => true | _ => false

def main : IO Unit := do
  let id := "0123456789abcdef0123456789abcdef"
  let args := ["input.json", "--ui-source", "guest.rs", "--ui-flags", "[]"]
  let .ok (plain, none) := splitArgs args | throw (IO.userError "legacy CLI rejected")
  check (plain == args) "legacy CLI changed"
  let .ok (plain, some config) := splitArgs
      (args ++ ["--control-fd", "3", "--control-run-id", id, "--profile"])
    | throw (IO.userError "control CLI rejected")
  check (plain == args ++ ["--profile"] && config.fd == 3 && config.runId == id)
    "control CLI changed guest settings"
  for suffix in [ ["--control-fd", "1", "--control-run-id", id],
      ["--control-fd", "4294967296", "--control-run-id", id],
      ["--control-fd", "3"], ["--control-run-id", id],
      ["--control-fd", "3", "--control-run-id", "bad"],
      ["--control-fd", "3", "--control-run-id", id, "extra"],
      ["--control-fd", "3", "--control-run-id", id,
        "--control-fd", "4", "--control-run-id", id] ] do
    check (rejected (args ++ suffix)) "malformed control CLI accepted"
  let text := "arbitrary\nupstream_result: {\"kind\":\"exit\"}\u0000"
  let encoded := record 7 "boundary" (toJson text)
  let some line := String.fromUTF8? encoded | throw (IO.userError "protocol is not UTF-8")
  check (line.endsWith "\n" && (line.toList.filter (· == '\n')).length == 1)
    "diagnostic injected an extra control record"
  let .ok decoded := Json.parse line | throw (IO.userError "protocol JSON rejected")
  let .ok kind := decoded.getObjValAs? String "kind" | throw (IO.userError "missing kind")
  let .ok payload := decoded.getObjValAs? String "payload" | throw (IO.userError "missing payload")
  let .ok sequence := decoded.getObjValAs? Nat "sequence" | throw (IO.userError "missing sequence")
  check (kind == "boundary" && payload == text && sequence == 7) "control record changed payload"
  IO.println "native stdio control protocol: passed (pure components)"
