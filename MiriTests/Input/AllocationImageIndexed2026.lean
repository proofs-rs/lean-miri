import Miri.Memory.MemoryState
import Miri.Input.AllocationImage

open Miri.Memory Miri.ABI Miri.Input

private def aid (n : UInt64) (h : n ≠ 0) : AllocId := ⟨n, h⟩

private def payloadTag : Option GlobalAllocationPayload → Nat
  | none => 0
  | some (.memory _) => 1
  | some .function => 2
  | some .vtable => 3
  | some .typeId => 4
  | some (.static ..) => 5

def main : IO Unit := do
  let firstId := aid 7 (by decide)
  let otherId := aid 8 (by decide)
  let first : GlobalAllocation := ⟨firstId, .memory, .ZERO, .ONE, .Not, none⟩
  let duplicate : GlobalAllocation := ⟨firstId, .static, .ofBytes 4, .ONE, .Mut, none⟩
  let other : GlobalAllocation := ⟨otherId, .function, .ZERO, .ONE, .Not, none⟩
  let initial : MemoryState Unit Unit Unit :=
    MemoryState.setGlobalEntries MemoryState.empty #[first, duplicate, other]
  let updated := initial.setGlobalPayload firstId .function
  let originalMap := initial.mapGlobals fun row =>
    if row.allocId == firstId then {row with payload := some .function} else row
  let summary := fun (row : GlobalAllocation) =>
    (row.allocId, row.kind, row.size, row.align, row.mutability, payloadTag row.payload)
  unless updated.globals.map summary == originalMap.globals.map summary do
    throw (IO.userError "indexed payload update differs from the original full map")
  let missing := initial.setGlobalPayload (aid 99 (by decide)) .vtable
  unless missing.globals.map summary == initial.globals.map summary do
    throw (IO.userError "missing runtime ID changed global rows")
  let rows := updated.globals
  unless rows.size == 3 do throw (IO.userError "indexed payload update changed row count")
  unless (rows[0]?.map fun row => payloadTag row.payload) == some 2 do
    throw (IO.userError "indexed payload update missed first duplicate row")
  unless (rows[1]?.map fun row => payloadTag row.payload) == some 2 do
    throw (IO.userError "indexed payload update missed later duplicate row")
  unless (rows[2]?.map fun row => (row.allocId, row.kind, row.size, row.align, row.mutability, payloadTag row.payload)) ==
      some (other.allocId, other.kind, other.size, other.align, other.mutability, payloadTag other.payload) do
    throw (IO.userError "indexed payload update changed unrelated row")
  unless initial.globals.map (fun row => (row.allocId, row.kind, payloadTag row.payload)) ==
      #[(first.allocId, first.kind, payloadTag first.payload), (duplicate.allocId, duplicate.kind, payloadTag duplicate.payload),
        (other.allocId, other.kind, payloadTag other.payload)] do
    throw (IO.userError "indexed payload update mutated the input state")

  let memoryNode : AllocationNode := {
    id := 12, status := .supported, kind := .memory,
    data := some (.memory ⟨2, 1, .immutable, "ff", #[], #[]⟩),
    memory := none, payload := Lean.Json.null
  }
  let functionNode : AllocationNode := {
    id := 11, status := .supported, kind := .typeId,
    data := some (.typeId 0), memory := none, payload := Lean.Json.null
  }
  let result := AllocationImage.importGraph RuntimeTargetDataLayout.default #[]
    { staticInfo := fun _ => throw "unexpected static query" } #[functionNode, memoryNode]
    (MemoryState.empty : MemoryState CtfeProvenance Unit Unit)
  match result.outcome with
  | .error message => unless message == "allocation byte size mismatch" do
      throw (IO.userError s!"unexpected importGraph error: {message}")
  | .ok _ => throw (IO.userError "malformed allocation image unexpectedly imported")
  unless result.memory.nextAllocId == 3 && result.memory.importedGlobalIds.size == 2 do
    throw (IO.userError "failed import lost its consumed registration prefix")
  let importedRows := result.memory.globals
  unless importedRows.size == 2 do throw (IO.userError "failed import lost registered global rows")
  unless (importedRows[0]?.map fun row => payloadTag row.payload) == some 4 do
    throw (IO.userError "failed import lost earlier type-id payload")
  unless (importedRows[1]?.map fun row => payloadTag row.payload) == some 0 do
    throw (IO.userError "failed import unexpectedly populated malformed image")

  let sourceFirst : AllocationNode := {
    id := 42, status := .supported, kind := .typeId,
    data := some (.typeId 1), memory := none, payload := .str "first"
  }
  let sourceDuplicate : AllocationNode := {
    sourceFirst with payload := .str "duplicate"
  }
  let indexedManual := AllocationImage.Imported.withSourceIndex
    #[sourceFirst, sourceDuplicate] #[]
  let fallbackManual := AllocationImage.Imported.ofSource
    #[sourceFirst, sourceDuplicate] #[]
  let sourceRegistration := MemoryLifecycle.registerImportedGlobal
    (MemoryState.empty : MemoryState CtfeProvenance Unit Unit) () 42 .typeId
    .ZERO .ONE .Not
  let sourceMemory := sourceRegistration.memory
  let sourceRuntimeId ← match sourceRegistration.outcome with
    | .ok id => pure id
    | .error error => throw (IO.userError s!"source identity setup failed: {error}")
  for image in #[indexedManual, fallbackManual] do
    match image.sourceNode sourceMemory sourceRuntimeId with
    | .ok node => unless node == sourceFirst do
        throw (IO.userError "source lookup did not preserve first duplicate")
    | .error error => throw (IO.userError s!"source lookup failed: {error}")
  unless indexedManual.source == #[sourceFirst, sourceDuplicate] &&
      fallbackManual.source == #[sourceFirst, sourceDuplicate] &&
      indexedManual.initializers.isEmpty && fallbackManual.initializers.isEmpty do
    throw (IO.userError "source index changed public image data")

  let absentSourceRegistration := MemoryLifecycle.registerImportedGlobal
    sourceMemory () 99 .typeId .ZERO .ONE .Not
  let absentSourceId ← match absentSourceRegistration.outcome with
    | .ok id => pure id
    | .error error => throw (IO.userError s!"missing-source setup failed: {error}")
  for image in #[indexedManual, fallbackManual] do
    match image.sourceNode absentSourceRegistration.memory absentSourceId with
    | .error error => unless error == "imported global source node is unavailable" do
        throw (IO.userError s!"missing-source error changed: {error}")
    | .ok _ => throw (IO.userError "missing source node unexpectedly resolved")
  match indexedManual.sourceNode sourceMemory (aid 77 (by decide)) with
  | .error error => unless error == "runtime global has no imported source identity" do
      throw (IO.userError s!"missing-runtime error changed: {error}")
  | .ok _ => throw (IO.userError "missing runtime identity unexpectedly resolved")

  let successfulImport := AllocationImage.importGraph RuntimeTargetDataLayout.default #[]
    { staticInfo := fun _ => throw "unexpected static query" } #[functionNode]
    (MemoryState.empty : MemoryState CtfeProvenance Unit Unit)
  match successfulImport.outcome with
  | .error message => throw (IO.userError s!"valid source image failed to import: {message}")
  | .ok image =>
      unless image.source == #[functionNode] && image.initializers.isEmpty do
        throw (IO.userError "imported source index changed public image data")
      let some runtimeId := successfulImport.memory.runtimeIdForExport? functionNode.id
        | throw (IO.userError "successful import lost source runtime mapping")
      match image.sourceNode successfulImport.memory runtimeId with
      | .ok node => unless node == functionNode do
          throw (IO.userError "successful import source index returned a different node")
      | .error error => throw (IO.userError s!"successful import source lookup failed: {error}")
  IO.println "indexed global payload update preserves duplicate rows, order, and unrelated entries"

#print axioms Miri.Memory.KeyedArray.modifyAt
#print axioms Miri.Memory.KeyedArray.mapValuesForKey
#print axioms Miri.Memory.MemoryState.setGlobalPayload
