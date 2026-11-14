import Miri.Input.ProfileDocument
import Miri.Input.CompilerInitialAllocationPreparation
import Miri.Input.CompilerColdU64Engine
open Lean Miri Miri.Input Miri.Memory Miri.Interpreter
private def must {A : Type} : Except String A → IO A
  | .ok value => pure value
  | .error error => throw (IO.userError error)

/-- Source and boundary are inputs; the independent result is opened only after
actual fixed-Step execution. No expected value, physical index or root ID is
embedded in this control. This is a cold pre-runtime leaf comparison. -/
def main (args : List String) : IO Unit := do
  let [documentPath,boundaryPath,oraclePath] := args
    | throw (IO.userError "expected paired full source document, cold boundary, independent oracle")
  let decoded ← must (ProfileDocument.decodeProfiled (← IO.FS.readFile documentPath) {})
  let .initial document := decoded | throw (IO.userError "complete initial allocation profile required")
  let program ← must (lowerProgram document.input.document)
  let setup ← must (EvalPreparation.prepareCompilerProfiled {} program)
  let candidates := document.input.document.ctfeScalarSources.filter fun frame =>
    match frame.program with
    | .rawU64 raw => raw.required.isEmpty && raw.ownerKind == .associatedConstant
    | _ => false
  let [frame] := candidates.toList | throw (IO.userError "expected unique actual external cold u64 leaf")
  let source ← must (CompilerColdU64Source.prepare setup.compiler frame)
  let boundaryJson ← must (Json.parse (← IO.FS.readFile boundaryPath))
  let boundary ← must (CompilerColdU64Source.ColdBoundary.read source.registered boundaryJson)
  let target := setup.compiler.runtime.target.base
  let (snapshot,arena) ← must (CompilerInitialAllocation.SymbolBridge.decode
    (target.pointerWidth.bits / 8) (target.endian == .little) document.snapshot source.types.arena)
  let (symbols,arena) ← must (CompilerInitialAllocation.StaticMaterial.prepare setup.compiler.runtime snapshot arena)
  let types := {source.types with arena}
  must (CompilerColdU64Source.verify source.registered types)
  let run := 1
  let (installed,world) := CompilerInitialAllocation.installAtomic
    (snapshot.next.toNat + 1) symbols run snapshot
    ({memory := .empty} : CompilerInitialAllocation.AllocatorWorld Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
  must installed
  let imported := AllocationImage.importGraph setup.compiler.runtime.target
    setup.compiler.program.compilerTables.definitions CompilerGlobals.queries #[] world.memory
  let image ← must imported.outcome
  let world := world.store.withMemory imported.memory
  let actual := CompilerColdU64Engine.run setup.compiler image types source.registered boundary source.registered.allocationKey world
  let result ← must actual.outcome
  unless !actual.blocked && result.type == source.registered.type && !result.pcs.isEmpty do
    throw (IO.userError "actual source engine failed identity/PC/completion checks")
  -- The oracle is never supplied to the engine or to source registration.
  let oracle ← must (Json.parse (← IO.FS.readFile oraclePath))
  let initial ← must (oracle.getObjVal? "initial")
  for field in ["next_source_alloc_id","global_count","dedup_count","globals","dedup"] do
    unless (← must (initial.getObjVal? field)) == (← must (document.snapshot.getObjVal? field)) do
      throw (IO.userError s!"paired initial compiler state differs: {field}")
  let acquired ← must (oracle.getObjVal? "after_source_acquisition")
  for field in ["next_source_alloc_id","global_count","dedup_count","globals","dedup"] do
    unless (← must (acquired.getObjVal? field)) == (← must (initial.getObjVal? field)) do
      throw (IO.userError s!"source acquisition changed frozen allocation state: {field}")
  let expectedPcs ← must (oracle.getObjValAs? (Array (Nat × Nat)) "selected_pcs")
  unless result.pcs == expectedPcs do
    throw (IO.userError "actual source PCs differ from independent selected Rust trace")
  let expected ← must (oracle.getObjVal? "result")
  let expectedSource ← must (expected.getObjValAs? Nat "source_alloc_id")
  let expectedBits ← must (expected.getObjValAs? String "bits_unsigned")
  unless expectedSource > 0 && expectedSource < 2^64 && (← must (expected.getObjValAs? Nat "size_bytes")) == 8 && expectedBits == toString result.value.toNat &&
      actual.allocations.memory.initialCompilerSource? run result.root == some (UInt64.ofNat expectedSource) do
    throw (IO.userError "actual allocated-root identity/scalar differs from independent PA oracle")
  let after ← must (oracle.getObjVal? "after_evaluated_root")
  let afterNext ← must (after.getObjValAs? Nat "next_source_alloc_id")
  unless afterNext > 0 && afterNext < 2^64 && actual.allocations.runs.any (fun row => row.1 == run && row.2.toNat == afterNext) do
    throw (IO.userError "actual central frontier differs from independent PA oracle")
  let rows ← must ((← must (after.getObjVal? "globals")).getArr?)
  let some row := rows.find? (fun row => row.getObjValAs? Nat "source_alloc_id" == .ok expectedSource)
    | throw (IO.userError "oracle root global absent")
  let rootSymbols : CompilerInitialAllocation.Symbols := {
    pointerBytes := (target.pointerWidth.bits / 8),littleEndian := target.endian == .little
    function := fun _ => .error "root memory cannot contain a function key"
    type := fun _ => .error "root memory cannot contain a type key"
    predicates := fun _ => .error "root memory cannot contain predicates" }
  let key ← must (CompilerInitialAllocation.readSourceMemory rootSymbols (UInt64.ofNat afterNext) (← must (row.getObjVal? "value")))
  unless actual.allocations.symbolic.any (fun row => row.1 == result.root && row.2 == .memory key) do
    throw (IO.userError "full actual root MemoryKey differs from independent PA oracle")
  unless actual.allocations.typedDedup.size == world.typedDedup.size &&
      actual.allocations.typedDedup.all (fun row => world.typedDedup.any fun old => old.run == row.run && old.runtime == row.runtime && old.salt == row.salt && old.key == row.key) &&
      (← must (after.getObjVal? "dedup")) == (← must (initial.getObjVal? "dedup")) do
    throw (IO.userError "typed dedup changed during pointer-free PA allocation")
  unless result.valtree.root == 0 && result.valtree.nodes == #[.Leaf result.value.toNat 8] do
    throw (IO.userError "immutable scalar ValTree reader differs from actual allocated value")
  IO.println s!"PASS actual fixed-Step external u64 leaf; value={result.value}; PCs={result.pcs.size}; full root key/counter/dedup/ValTree match paired independent Rust oracle"
