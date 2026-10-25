import Miri.Memory.MemoryState

open Miri.ABI Miri.Memory

private def check (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def main : IO Unit := do
  let some id1 := AllocId.ofUInt64 1
    | throw (IO.userError "missing first allocation ID")
  let some id2 := AllocId.ofUInt64 2
    | throw (IO.userError "missing second allocation ID")
  let first : GlobalAllocation :=
    {allocId := id1, kind := .static, size := Size.ZERO, align := Align.ONE}
  let later : GlobalAllocation :=
    {allocId := id1, kind := .function, size := Size.ZERO, align := Align.ONE}
  let other : GlobalAllocation :=
    {allocId := id2, kind := .vtable, size := Size.ZERO, align := Align.ONE}
  let empty : MemoryState Provenance Unit Unit := .empty
  let globals := empty.setGlobalEntries #[first, other, later]
  check ((globals.findGlobal? id1).map (fun row => row.kind) == some .static)
    "first duplicate global row changed"
  check ((globals.globalsForId id1).size == 2) "duplicate global rows lost"
  check (globals.hasFunctionPointer id1) "later duplicate function row ignored"
  check ((globals.findGlobal? id2).map (fun row => row.kind) == some .vtable)
    "different global ID changed"
  let remapped := globals.mapGlobals (fun row =>
    if row.allocId == id1 then {row with allocId := id2} else row)
  check ((remapped.findGlobal? id1).isNone) "old key survived payload key change"
  check ((remapped.globalsForId id2).size == 3) "mapped rows lost source order"
  check ((remapped.findGlobal? id2).map (fun row => row.kind) == some .static)
    "mapped first row changed"
  let imported := empty.setImportedGlobalIds #[(7, id1), (9, id2), (7, id2)]
  check (imported.runtimeIdForExport? 7 == some id1) "first export mapping changed"
  check (imported.importedGraphIdForRuntime? id2 == some 9)
    "first reverse runtime mapping changed"
  let sourceIds := empty.setSourceAllocIdCrosswalks
    #[(id1, 71), (id2, 72), (id1, 73)] #[(71, id1), (72, id2), (71, id2)]
  check (sourceIds.sourceAllocIdForRuntime? id1 == some 71)
    "first raw-source ID mapping changed"
  check (sourceIds.runtimeForSourceAllocId? 71 == some id1)
    "first reverse raw-source mapping changed"
  IO.println "MemoryState duplicate first-row, later any-row, rekey and crosswalk: PASS"
