import Miri.Input.EvalPreparation
import Miri.Input.EvalMiriHostEffectsConstruction

open Miri Miri.Input Miri.Memory Miri.Interpreter

private def must {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: SelectedAllocIdCatalog157 <prepared export.json> [selected|root]")
  let profile := args[1]?.getD "selected"
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let program ← must (lowerProgram decoded.document)
  let attempt := EvalPreparation.prepare program
  let prepared ← must attempt.outcome
  let memory := attempt.memory
  let some world := prepared.compiler.program.input.compilerAllocIdWorld |
    throw (IO.userError "prepared exporter output omitted compiler_alloc_id_world")
  check memory.sourceAllocIdWorldActive "prepared raw AllocId crosswalk is inactive"
  check (world.rawPool.size == world.lastReservedSourceAllocId.toNat)
    "raw AllocId pool size differs from its frontier"
  for (row, index) in world.rawPool.toList.zipIdx do
    check (row.sourceAllocId.toNat == index + 1) s!"raw AllocId pool is not contiguous at {index}"
  let some sentinel := world.rawPool[world.rawPool.size - 1]? |
    throw (IO.userError "prepared raw AllocId sentinel is absent")
  check (sentinel.kind == .dangling && sentinel.status == .dangling && sentinel.allocationId.isNone)
    "prepared raw AllocId sentinel is not the final dangling reservation"
  check (world.nextSourceAllocId.toNat == world.lastReservedSourceAllocId.toNat + 1)
    "prepared next source AllocId does not follow the final sentinel"

  let functionRows := world.dedupCatalog.filter (·.keyKind == .function)
  let vtableRows := world.dedupCatalog.filter (·.keyKind == .vtable)
  if profile == "root" then
    check (functionRows.isEmpty && vtableRows.isEmpty) "root_u32 unexpectedly selected function/vtable keys"
  else
    check (!functionRows.isEmpty) "fixture did not select a compiler function key"
    check (!vtableRows.isEmpty) "fixture did not select a compiler vtable key"
  let functionRegistry ← must (CompilerFunctionPointers.seedImported
    prepared.compiler.pointers prepared.image memory (FunctionPointers.Registry.empty (Other := String)))
  let vtableRegistry ← must (CompilerVTableMachine.seedImported
    prepared.compiler.vtables prepared.image memory VTableMachine.Registry.empty)
  let mut functionResults := 0
  for row in functionRows do
    check (row.salts.size == 32) "selected function row does not contain all 32 source salts"
    for result in row.salts do
      let runtimeId ← must (AllocationImage.runtimeId memory result.allocationId)
      check (memory.sourceAllocIdForRuntime? runtimeId == some result.sourceAllocId)
        s!"function salt {result.salt} is not bound to its exact raw source AllocId"
      check (functionRegistry.functions.any (fun entry =>
        entry.salt.val == result.salt && entry.allocation == runtimeId))
        s!"selected function salt {result.salt} did not seed the actual function registry"
      functionResults := functionResults + 1
  let mut vtableResults := 0
  for row in vtableRows do
    check (row.salts.size == 32) "selected vtable row does not contain all 32 source salts"
    for result in row.salts do
      let runtimeId ← must (AllocationImage.runtimeId memory result.allocationId)
      check (memory.sourceAllocIdForRuntime? runtimeId == some result.sourceAllocId)
        s!"vtable salt {result.salt} is not bound to its exact raw source AllocId"
      check (vtableRegistry.entries.any (fun entry =>
        entry.salt.val == result.salt && entry.allocation == runtimeId))
        s!"selected vtable salt {result.salt} did not seed the actual vtable registry"
      vtableResults := vtableResults + 1
  IO.println s!"source157 prepared-world PASS: profile={profile}, raw-prefix={world.rawPool.size}, function-keys={functionRows.size} function-results={functionResults}, vtable-keys={vtableRows.size} vtable-results={vtableResults}"
