import Miri.Input.Decoder
import Miri.Input.AllocationImage

open Miri.Input

private def must (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let directory := args.headD "scratch/compact-allocation-inputs"
  let load := fun name => IO.FS.readFile s!"{directory}/{name}.json"
  for name in #["valid-noncontiguous-salts", "valid-grouped-without-world", "valid-shared-bytes-cycle", "valid-body-tls-image"] do
    let decoded ← must (decodeJson (← load name))
    if name == "valid-noncontiguous-salts" then
      let some world := decoded.document.compilerAllocIdWorld |
        throw (IO.userError "noncontiguous control lost the source world")
      let some row := world.dedupCatalog[0]? | throw (IO.userError "function salt row absent")
      check (row.salts.size == 32) "function group lost salt results"
      for (result, index) in row.salts.toList.zipIdx do
        check (result.salt == index && result.allocationId == index + 1 &&
            result.sourceAllocId.toNat == 2 * index + 3)
          s!"salt {index} lost its distinct graph/source identities"
      check (decoded.document.allocations.size == 33) "function group did not retain every identity"
    if name == "valid-shared-bytes-cycle" then
      let nodes := decoded.document.allocations
      let some firstNode := nodes[0]? | throw (IO.userError "first node absent")
      let some secondNode := nodes[1]? | throw (IO.userError "second node absent")
      check (nodes.size == 2 && firstNode.id == 0 && secondNode.id == 1 &&
          firstNode.sourceAllocId == some 7 && secondNode.sourceAllocId == some 19)
        "shared bytes merged allocation identities"
      let some first := firstNode.memory | throw (IO.userError "first memory absent")
      let some second := secondNode.memory | throw (IO.userError "second memory absent")
      let some firstEdge := first.relocations[0]? | throw (IO.userError "first edge absent")
      let some secondEdge := second.relocations[0]? | throw (IO.userError "second edge absent")
      let some firstInit := first.initializationRanges[0]? | throw (IO.userError "first init absent")
      let some secondInit := second.initializationRanges[0]? | throw (IO.userError "second init absent")
      check (first.bytesHex == second.bytesHex && first.mutability == .immutable &&
          second.mutability == .mutable && firstEdge.target == 1 &&
          secondEdge.target == 0 && firstEdge.immutable &&
          firstEdge.sharedRef && firstInit.initialized &&
          !secondInit.initialized)
        "shared byte image changed initialization, provenance flags or cyclic graph edges"
      let imported := AllocationImage.importGraph Miri.ABI.RuntimeTargetDataLayout.default #[]
        { staticInfo := fun _ => throw "unexpected static query" } nodes
        ({Miri.Memory.MemoryState.empty with nextAllocId := 100} :
          Miri.Memory.MemoryState Miri.Memory.CtfeProvenance Unit Unit)
      let image ← must imported.outcome
      let firstId ← must (AllocationImage.runtimeId imported.memory 0)
      let secondId ← must (AllocationImage.runtimeId imported.memory 1)
      check (firstId != secondId && imported.memory.globals.size == 2)
        "shared bytes merged runtime allocation identities"
      let firstSource ← must (image.sourceNode imported.memory firstId)
      let secondSource ← must (image.sourceNode imported.memory secondId)
      check (firstSource.sourceAllocId == some 7 && secondSource.sourceAllocId == some 19)
        "import changed exact source identity witnesses"
      let some firstGlobal := imported.memory.findGlobal? firstId |
        throw (IO.userError "first imported global absent")
      let some secondGlobal := imported.memory.findGlobal? secondId |
        throw (IO.userError "second imported global absent")
      let some (.memory firstAllocation) := firstGlobal.payload |
        throw (IO.userError "first imported memory payload absent")
      let some (.memory secondAllocation) := secondGlobal.payload |
        throw (IO.userError "second imported memory payload absent")
      let some firstProvenance := firstAllocation.provenanceMap.getPtr Miri.ABI.Size.ZERO |
        throw (IO.userError "first imported provenance absent")
      let some secondProvenance := secondAllocation.provenanceMap.getPtr Miri.ABI.Size.ZERO |
        throw (IO.userError "second imported provenance absent")
      let firstInitialized ← must (firstAllocation.initializationMask.get Miri.ABI.Size.ZERO |>.mapError toString)
      let secondInitialized ← must (secondAllocation.initializationMask.get Miri.ABI.Size.ZERO |>.mapError toString)
      check (firstProvenance.intoParts == (secondId, true, true) &&
          secondProvenance.intoParts == (firstId, true, true) &&
          firstInitialized && !secondInitialized && firstAllocation.mutability == .Not &&
          secondAllocation.mutability == .Mut)
        "runtime import changed cycle targets, CTFE provenance flags or independent initialization"
    IO.println s!"PASS {name}"
  let foreignDeclaration ← load "valid-foreign-tls-declaration"
  let validForeign ← must (JsonReader.run (DecoderValues.parseThreadLocal "$thread_local") foreignDeclaration)
  check (validForeign.info.foreignItem && validForeign.initializer.isNone)
    "foreign TLS declaration without an initializer changed"
  let invalidForeign ← load "foreign-tls-declaration-image"
  check (!(JsonReader.run (DecoderValues.parseThreadLocal "$thread_local") invalidForeign).isOk)
    "foreign TLS codec discarded an unchecked initializer"
  for name in #["foreign-body-tls-image", "dangling-body-tls-image", "unmatched-raw-null", "null-sentinel", "node-at-opaque-source",
      "duplicate-salt-result", "short-salts", "missing-function-key", "opaque-eligible-byte-image",
      "obsolete-schema", "missing-byte-image", "zero-group-source-id",
      "zero-source-id", "duplicate-source-id", "duplicate-graph-id", "shuffled-group-identities",
      "empty-function-group", "dangling-byte-image", "duplicate-byte-image"] do
    match decodeJson (← load name) with
    | .error message => IO.println s!"PASS {name}: {message}"
    | .ok _ => throw (IO.userError s!"malformed compact allocation accepted: {name}")
