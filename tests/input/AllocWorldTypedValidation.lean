import Miri.Input.Decoder
import Miri.Input.AllocIdWorldValidation

open Miri.Input
private def must {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)
private def check (condition : Bool) (reason : String) : IO Unit :=
  unless condition do throw (IO.userError reason)

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "expected prepared-world export")
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile path))
  let input := decoded.document
  let some world := input.compilerAllocIdWorld | throw (IO.userError "fixture has no prepared world")
  let clean := {input with raw := .null, sharedNodes := #[]}
  let _ ← must (AllocIdWorldValidation.validate clean)
  let reject := fun world => !(AllocIdWorldValidation.validate {clean with compilerAllocIdWorld := some world}).isOk
  check (reject {world with nextSourceAllocId := 0}) "zero frontier accepted"
  check (reject {world with finalSentinelSourceAllocId := world.nextSourceAllocId}) "sentinel mismatch accepted"
  check (reject {world with rawPool := #[]}) "missing pool coverage accepted"
  let some row := world.rawPool[0]? | throw (IO.userError "fixture pool empty")
  check (reject {world with rawPool := world.rawPool.set! 0 {row with sourceAllocId := 0}})
    "noncontiguous source identity accepted"
  if let some node := clean.allocations[0]? then
    let duplicate := {clean with allocations := clean.allocations.push node}
    check (!(AllocIdWorldValidation.validate duplicate).isOk) "duplicate graph identity accepted"
  if let some dedup := world.dedupCatalog[0]? then
    check (reject {world with dedupCatalog := world.dedupCatalog.set! 0 {dedup with salts := #[]}})
      "empty salt catalog accepted"
  IO.println s!"typed prepared-world validation PASS {path}"
