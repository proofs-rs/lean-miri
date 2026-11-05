import Miri.Input.Decoder

open Lean Miri.Input

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def set (raw : Json) (key : String) (value : Json) : Json :=
  Json.mkObj ((key, value) :: (raw.getObj?.toOption.map (·.toList) |>.getD []).filter (·.1 != key))

/-- Use a genuine prepared export: the old independent revalidation remains the
oracle. Mutating any indexed input requires dropping the dependent witness. -/
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected prepared JSON or binary export")
  let decoded ← must (decodeRuntimeBytesProfiled (← IO.FS.readBinFile path) {})
  let document := decoded.document
  check document.allocationParseBinding.isSome "checked graph lost allocation origin"
  check document.validateAllocationWorld.isOk "original raw/model revalidation failed"
  check (document.validateAllocationWorldForRun == document.validateAllocationWorld)
    "origin path differs from original revalidation"
  let some world := document.compilerAllocIdWorld | throw (IO.userError "fixture needs allocation world")
  let changedWorld := { world with nextSourceAllocId := world.nextSourceAllocId + 1 }
  let foreignWorld := { document with
    compilerAllocIdWorld := some changedWorld,
    allocationWorldValidation := none, allocationParseBinding := none }
  check (!foreignWorld.validateAllocationWorldForRun.isOk) "foreign typed world accepted"
  let some node := document.allocations[0]? | throw (IO.userError "fixture needs allocation rows")
  let changedNodes := document.allocations.set! 0 { node with id := node.id + 1000000 }
  let foreignNodes := { document with
    allocations := changedNodes,
    allocationWorldValidation := none, allocationParseBinding := none }
  check (!foreignNodes.validateAllocationWorldForRun.isOk) "foreign typed allocation accepted"
  let foreignRaw := { document with
    raw := set document.raw "compiler_alloc_id_world" .null,
    allocationWorldValidation := none, allocationParseBinding := none }
  check (!foreignRaw.validateAllocationWorldForRun.isOk) "foreign raw world accepted"
  let changedRows := { document with
    raw := set document.raw "allocations" (.arr #[]),
    allocationWorldValidation := none, allocationParseBinding := none }
  check (!changedRows.validateAllocationWorldForRun.isOk) "foreign raw allocations accepted"
  IO.println "allocation parse origin: original validator and foreign raw/model rejection PASS"
