import Miri.Frontend.FoundationGlobalBytes

open Lean Miri Miri.Frontend.Foundation

private def expect (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def rejects (r : Except String α) : IO Unit :=
  match r with | .error _ => pure () | .ok _ => throw (IO.userError "missing material accepted")

-- Synthetic memory images test the checked component, not source correspondence.
private def image : Input.AllocationMemory := {
  sizeBytes := 8, alignBytes := 1, mutability := .immutable,
  bytesHex := .image (Array.replicate 8 0),
  initializationRanges := #[⟨true, 0, 8⟩], relocations := #[] }
private def node (id : Nat) (value : Input.AllocationMemory) : Input.AllocationNode := {
  id, kind := .memory, memory := some value, data := some (.memory value) }

def main (args : List String) : IO Unit := do
  check ((← expect (globalByteCandidate image)).isSome) "immutable byte candidate omitted"
  check ((← expect (globalByteCandidate {image with mutability := .mutable})).isNone) "mutable candidate"
  check ((← expect (globalByteCandidate {image with alignBytes := 2})).isNone) "aligned candidate"
  check ((← expect (globalByteCandidate {image with initializationRanges := #[⟨false, 0, 8⟩]})).isNone) "uninitialized candidate"
  rejects (globalByteCandidate {image with initializationRanges := #[]})
  rejects (globalByteCandidate {image with sizeBytes := 9})
  let packed ← expect ((Memory.CtfeProvenance.fromParts (⟨1, by decide⟩, true, true)).mapError reprStr)
  let relocation : Input.Relocation := ⟨0, 0, "0000000000000000", true, true, packed⟩
  let pointerImage := {image with relocations := #[relocation]}
  check ((← expect (globalByteCandidate pointerImage)).isNone) "provenance-bearing candidate"
  let nodes := #[node 0 pointerImage]
  let imported := importMemoryGraph ABI.RuntimeTargetDataLayout.default nodes
    (Memory.MemoryState.empty : Memory.MemoryState Unit Unit Unit)
  let _ ← expect imported.outcome
  let runtimeId ← expect (Input.AllocationImage.runtimeId imported.memory 0)
  let some global := imported.memory.globals[0]? | throw (IO.userError "global missing")
  let some (.memory allocation) := global.payload | throw (IO.userError "memory payload missing")
  let some provenance := allocation.provenanceMap.getPtr ABI.Size.ZERO | throw (IO.userError "provenance missing")
  check (provenance.allocId == runtimeId && provenance.immutable && provenance.sharedRef) "CTFE identity/flags not preserved"
  let invalidFlags := {pointerImage with relocations := #[{relocation with sharedRef := false}]}
  let rejected := importMemoryGraph ABI.RuntimeTargetDataLayout.default #[node 0 invalidFlags]
    (Memory.MemoryState.empty : Memory.MemoryState Unit Unit Unit)
  rejects rejected.outcome
  check (rejected.memory.globals.size == 1) "failed import lost reserved allocation prefix"
  check (allocation.len == 8 && allocation.mutability == .Not) "memory image changed"
  let [path] := args | throw (IO.userError "usage: FoundationGlobalBytes FOUNDATION_JSON")
  let source ← IO.FS.readFile path
  let document ← expect (Json.parse source >>= decode)
  let initial := PhysicalTypeRegistry.start document
  let (r, emptyCatalog) ← expect (globalBytesWithoutCandidates initial #[])
  check (emptyCatalog.coveredAllocations.isEmpty && emptyCatalog.candidates.isEmpty && emptyCatalog.saltCount == 32) "empty graph catalog"
  let (str, _) ← expect (r.lookup emptyCatalog.strType)
  check (str.shapeKind == .str) "str primitive identity"
  let (_, catalog) ← expect (globalBytesWithoutCandidates initial nodes)
  check (catalog.coveredAllocations == #[0] && catalog.candidates.isEmpty) "noncandidate coverage"
  rejects (globalBytesWithoutCandidates initial #[node 0 image])
  rejects (globalBytesWithoutCandidates initial #[node 1 pointerImage])
  IO.println "foundation global bytes: candidate boundary, coverage and checked provenance import passed"
