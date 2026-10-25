import Miri.Input.EvalPreparation
import Miri.Input.CompilerIntrinsicSymbols
import Miri.Interpreter.IntrinsicSymbolsMachine

open Miri Miri.ABI Miri.Input Miri.Memory Miri.Interpreter Miri.Concurrency
open MachineHooks (M State)

private structure TypeIdUser where
  registry : IntrinsicSymbolsMachine.Registry

private abbrev TypeIdState := MachineHooks.State MiriMemoryKind TypeIdUser

private def must {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def stateWith
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (registry : IntrinsicSymbolsMachine.Registry) : TypeIdState :=
  ⟨Stack.empty, {
    memory, borrowTracker := none, dataRace := none, threads := ThreadManager.initial false,
    raceAllocations := #[], allocationSpans := #[], user := ⟨registry⟩
  }⟩

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: SelectedStaticTypeIdRuntime162 <export.json>")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let program ← must (lowerProgram decoded.document)
  let attempt := EvalPreparation.prepare program
  let prepared ← must attempt.outcome
  let memory := attempt.memory
  let some world := prepared.compiler.program.input.compilerAllocIdWorld |
    throw (IO.userError "prepared export omitted compiler allocator world")
  check memory.sourceAllocIdWorldActive "prepared AllocId world is inactive"
  let staticRows := world.dedupCatalog.filter (·.keyKind == .static)
  let typeRows := world.dedupCatalog.filter (·.keyKind == .typeId)
  check (!staticRows.isEmpty) "fixture did not select a static key"
  check (!typeRows.isEmpty) "fixture did not select a TypeId key"
  for row in staticRows do
    check (row.salts.size == 1) "static key does not have one salt-zero outcome"
    let some result := row.salts[0]? | throw (IO.userError "static salt-zero outcome missing")
    check (result.salt == 0 && result.allocationId == row.keyAllocationId)
      "static result is not its exact salt-zero graph witness"
    let runtimeId ← must (AllocationImage.runtimeId memory row.keyAllocationId)
    check (memory.sourceAllocIdForRuntime? runtimeId == some result.sourceAllocId)
      "static result source ID differs from its prepared runtime allocation"

  let typeRegistry ← must (CompilerIntrinsicSymbols.seedImported prepared.compiler prepared.image memory
    IntrinsicSymbolsMachine.Registry.empty)
  for row in typeRows do
    check (row.salts.size == 1) "TypeId key does not have one salt-zero outcome"
    let some result := row.salts[0]? | throw (IO.userError "TypeId salt-zero outcome missing")
    check (result.salt == 0 && result.allocationId == row.keyAllocationId)
      "TypeId result is not its exact salt-zero graph witness"
    let runtimeId ← must (AllocationImage.runtimeId memory row.keyAllocationId)
    check (memory.sourceAllocIdForRuntime? runtimeId == some result.sourceAllocId)
      "TypeId result source ID differs from its prepared runtime allocation"
    let some ty ← must (CompilerIntrinsicSymbols.importedTypeId prepared.compiler prepared.image memory runtimeId) |
      throw (IO.userError "selected TypeId witness lacks an imported exact type")
    check (typeRegistry.typeIds.contains (runtimeId, ty))
      "selected exact TypeId key did not seed the live intrinsic registry"

  let access : IntrinsicSymbolsMachine.Access TypeIdUser := {
    get := fun user => user.registry
    put := fun user registry => {user with registry}
  }
  let some selected := typeRegistry.typeIds[0]? | throw (IO.userError "TypeId registry is empty")
  let state := stateWith memory typeRegistry
  let (hitState, hit) := MachineHooks.run (IntrinsicSymbolsMachine.reserveTypeId access selected.2) state
  match hit with
  | .ok id => check (id == selected.1) "TypeId registry hit returned a different allocation"
  | .error error => throw (IO.userError s!"TypeId registry hit failed: {reprStr error}")
  check (hitState.machine.memory.sourceAllocIdNext == memory.sourceAllocIdNext)
    "TypeId registry hit consumed a fresh source ID"
  let missingTy := selected.2 + 104729
  check (!(typeRegistry.typeIds.any (·.2 == missingTy))) "missing TypeId key collides with selected registry"
  let (missState, miss) := MachineHooks.run (IntrinsicSymbolsMachine.reserveTypeId access missingTy) state
  match miss with
  | .error (.unsupported message) =>
    check (message.contains "not captured") "TypeId miss returned the wrong unsupported reason"
  | .error error => throw (IO.userError s!"TypeId miss returned unexpected error: {reprStr error}")
  | .ok _ => throw (IO.userError "uncaptured TypeId key unexpectedly reserved")
  check (missState.machine.memory.sourceAllocIdNext == memory.sourceAllocIdNext)
    "TypeId miss changed the source frontier"
  check (missState.machine.user.registry.typeIds.size == typeRegistry.typeIds.size)
    "TypeId miss changed the prepared registry"
  IO.println s!"source162 selected static/TypeId PASS: static-keys={staticRows.size}, TypeId-keys={typeRows.size}, TypeId-registry={typeRegistry.typeIds.size}, live-hit/missing-Unsupported"
