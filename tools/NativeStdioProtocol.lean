import Lean

/-! Runner-owned control transport. These bytes never travel over guest
stdout/stderr; the parent owns a fresh inherited regular-file descriptor. -/
namespace NativeStdioProtocol
open Lean

structure Configuration where
  fd : UInt32
  runId : String
  deriving Repr

/-- Control options are a suffix (before optional --profile). Requiring both
options and an exact suffix prevents accidentally enabling host IO. -/
def splitArgs (args : List String) : Except String (List String × Option Configuration) := do
  let profile := args.getLast? == some "--profile"
  let base := if profile then args.dropLast else args
  let (base, configuration) ← match base.reverse with
    | runId :: "--control-run-id" :: rawFd :: "--control-fd" :: reversed => do
      let some fd := rawFd.toNat? | throw "control fd must be a decimal integer"
      unless fd >= 3 && fd < 2^32 do throw "control fd must be between 3 and u32::MAX"
      unless runId.length == 32 && runId.toList.all (fun c => c.isDigit || ('a' <= c && c <= 'f')) do
        throw "control run id must be 32 lowercase hexadecimal digits"
      let base := reversed.reverse
      if base.contains "--control-fd" || base.contains "--control-run-id" then
        throw "duplicate control options"
      pure (base, some {fd := UInt32.ofNat fd, runId})
    | _ => do
      if base.contains "--control-fd" || base.contains "--control-run-id" then
        throw "control fd and run id must form the final option pair"
      pure (base, none)
  pure (if profile then base ++ ["--profile"] else base, configuration)

def record (sequence : Nat) (kind : String) (payload : Json) : ByteArray :=
  ((Json.mkObj [("version", toJson (1 : Nat)), ("sequence", toJson sequence),
    ("kind", toJson kind), ("payload", payload)]).compress ++ "\n").toUTF8

end NativeStdioProtocol
