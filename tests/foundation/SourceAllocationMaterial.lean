import Miri.Frontend.FoundationAllocations
open Lean Miri Miri.Frontend.Foundation
private def checked {α : Type} (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine foundation_allocations source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let material ← checked (sourceAllocationMaterial document)
  unless material.images.size == 2 do throw (IO.userError "genuine literal source graph count changed")
  let contents ← material.images.mapM fun image => do
    let .memory memory := image.payload | throw (IO.userError "literal source unexpectedly not memory")
    checked memory.bytesHex.checkedBytes
  unless contents.contains "Miri".toUTF8.data && contents.contains "foundation-bytes".toUTF8.data do
    throw (IO.userError "typed compiler literal memory images differ from Rust fixture")
  let some first := material.images[0]? | throw (IO.userError "genuine source image missing")
  let some second := material.images[1]? | throw (IO.userError "genuine source image missing")
  let duplicate : Input.SourceAllocations.Material := ⟨#[first,{second with rawId := first.rawId}]⟩
  match Input.SourceAllocations.validate duplicate with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "duplicate raw CTFE identity accepted")
  let truncated : Input.SourceAllocations.Material := ⟨#[{first with id := 1}]⟩
  match Input.SourceAllocations.validate truncated with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "source graph index mismatch accepted")
  IO.println "typed source memory: genuine literal images retained; raw identity and dense graph index mutations reject"
