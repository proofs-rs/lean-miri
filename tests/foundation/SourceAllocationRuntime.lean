import Miri.Frontend.FoundationInput
import Miri.Input.SourceCompilerAllocations
import Miri.Input.CompilerGlobalBytes
open Lean Miri Miri.Frontend.Foundation
private def checked {α : Type} (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine allocation-entry foundation input")
  let decoded ← checked (decodeRunnerInputProfiled (← IO.FS.readFile path) {})
  let some initial := decoded.initialWorld | throw (IO.userError "normal source World missing")
  unless initial.canonical.allocations.isEmpty do throw (IO.userError "source images imported eagerly")
  let some material := initial.canonical.sourceMaterial | throw (IO.userError "typed source missing")
  let some images := material.allocations | throw (IO.userError "typed source graph missing")
  let some source := images.images[0]? | throw (IO.userError "genuine source root missing")
  let (world,id) ← checked (Input.SourceCompilerAllocations.demand initial 0)
  unless world.canonical.allocations.size == 1 do throw (IO.userError "demand did not preserve exact graph")
  let some node := world.canonical.allocations[id]? | throw (IO.userError "canonical allocation missing")
  unless node.sourceAllocId == some source.rawId do throw (IO.userError "raw CTFE witness changed")
  let some image := node.memory | throw (IO.userError "source memory payload missing")
  unless (← checked image.bytesHex.checkedBytes) == "source-memory".toUTF8.data do
    throw (IO.userError "source bytes changed")
  let (again,same) ← checked (Input.SourceCompilerAllocations.demand world 0)
  unless same == id && again.canonical.allocations.size == world.canonical.allocations.size do
    throw (IO.userError "repeated demand allocated duplicate graph identity")
  let metadata ← checked (Input.RuntimeMetadata.ofDocument initial.canonical |>.mapError toString)
  let imported ← checked (Input.SourceCompilerAllocations.importDemanded metadata.target world id
    (Memory.MemoryState.empty : Memory.MemoryState Unit Unit Unit))
  let _ ← checked imported.outcome
  let runtime ← checked (Input.AllocationImage.runtimeId imported.memory id)
  let some global := imported.memory.findGlobal? runtime | throw (IO.userError "runtime global missing")
  let some (.memory payload) := global.payload | throw (IO.userError "runtime source payload missing")
  unless (← checked (payload.inspectWithUninitAndPtrOutsideInterpreter 0 payload.len |>.mapError toString)) ==
      "source-memory".toUTF8.data do throw (IO.userError "runtime imported bytes changed")
  let repeated ← checked (Input.SourceCompilerAllocations.importDemanded metadata.target again id imported.memory)
  let _ ← checked repeated.outcome
  unless repeated.memory.globals.size == 1 && node.sourceAllocId == some source.rawId &&
      repeated.memory.importedGlobalIds == imported.memory.importedGlobalIds do
    throw (IO.userError "repeated import changed identity crosswalk")
  let program ← checked (Input.lowerProgram initial.canonical)
  let runtime ← checked (Input.RuntimeMetadata.ofDocument initial.canonical |>.mapError toString)
  let bytes ← checked (Input.CompilerGlobalBytes.prepare program runtime imported.memory)
  unless !bytes.evidenceAvailable && !imported.memory.byteGlobalKeysReady do
    throw (IO.userError "unavailable byte interner became a known empty answer")
  IO.println "normal source allocation demand: lazy canonical graph, exact raw witness and bytes, idempotent checked runtime import; byte-interner evidence stays unavailable"
