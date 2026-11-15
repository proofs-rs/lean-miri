import Miri.Frontend.FoundationAllocations

open Lean Miri Miri.Frontend.Foundation

private def expect (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def rejects (r : Except String α) : IO Unit :=
  match r with | .error _ => pure () | .ok _ => throw (IO.userError "invalid allocation material accepted")
private def replace (j : Json) (key : String) (value : Json) : Except String Json := do
  let fields ← j.getObj?
  return Json.mkObj ((fields.toArray.toList.filter (·.1 != key)) ++ [(key, value)])

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: FoundationAllocations FOUNDATION_JSON")
  let text ← IO.FS.readFile path
  let document ← expect (Json.parse text >>= decode)
  let nodes ← expect (sourceMemoryGraph document)
  check (nodes.size == 2) "expected two genuine literal source allocations"
  let images := nodes.filterMap (fun node => match node.data with
    | some (.memory image) => some image | _ => none)
  let bytes ← expect (images.mapM (·.bytesHex.checkedBytes))
  check (bytes.contains "Miri".toUTF8.data && bytes.contains "foundation-bytes".toUTF8.data) "source byte literal images changed"
  for node in nodes do
    check (node.sourceAllocId.isSome && node.memory.isSome) "source identity/image absent"
  let imported ← expect (importSourceMemory document
    (Memory.MemoryState.empty : Memory.MemoryState Unit Unit Unit))
  let _ ← expect imported.outcome
  check (imported.memory.globals.size == 2) "checked source import omitted allocation"
  for node in nodes do
    let runtimeId ← expect (Input.AllocationImage.runtimeId imported.memory node.id)
    let some runtime := imported.memory.globals.find? (·.allocId == runtimeId)
      | throw (IO.userError "runtime mapping absent")
    let some (.memory memory) := runtime.payload | throw (IO.userError "runtime source memory absent")
    let some source := node.memory | throw (IO.userError "source memory absent")
    let data ← expect ((memory.inspectWithUninitAndPtrOutsideInterpreter 0 memory.len).mapError toString)
    check (data == (← expect source.bytesHex.checkedBytes) && memory.mutability == .Not) "import altered compiler source image"
  for body in document.bodies do
    let blocks ← expect (body.getObjValAs? (Array Json) "blocks")
    let some block := blocks[0]? | throw (IO.userError "block absent")
    let statements ← expect (block.getObjValAs? (Array Json) "statements")
    let some statement := statements[0]? | throw (IO.userError "assignment absent")
    let source ← expect (statement.getObjVal? "value" >>= fun j => j.getObjVal? "operand" >>= fun j => j.getObjVal? "value")
    match ← expect (sourceAllocationConstant document source) with
    | .Slice allocation 16 => check (nodes[allocation]?.isSome) "slice graph reference"
    | .Scalar (.Ptr (.Allocation allocation 0 false false)) => check (nodes[allocation]?.isSome) "pointer graph reference"
    | _ => throw (IO.userError "compiler allocation constant form changed")
  -- The graph is available, but its eligible keys cannot fabricate salt misses.
  rejects (globalBytesWithoutCandidates (PhysicalTypeRegistry.start document) nodes)
  let rows ← expect (document.source.getObjValAs? (Array Json) "source_allocations")
  let some first := rows[0]? | throw (IO.userError "first source row missing")
  let changed ← expect (replace first "source_alloc_id" (toJson (0 : Nat)))
  let invalidSource ← expect (replace document.source "source_allocations" (.arr (rows.set! 0 changed)))
  rejects (sourceMemoryGraph {document with source := invalidSource})
  rejects (sourceAllocationConstant document (Json.mkObj [("kind",toJson "allocation_slice"),
    ("allocation",toJson (999 : Nat)),("metadata",toJson (0 : Nat))]))
  IO.println "foundation source allocations: genuine literal images/constants and checked import passed"
