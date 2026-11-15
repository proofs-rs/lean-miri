import Miri.Input.SourceCompilerArrays
import Miri.Input.SourceAggregateLayout
import Miri.Input.SourcePhysical
import Miri.Input.Decoder
open Miri Miri.Input Miri.Input.SourceCompilerWorld
private def checked (r : Except String α) : IO α := match r with
| .ok a => pure a | .error e => throw (IO.userError e)
private def check (value : Bool) (message : String) : IO Unit := unless value do throw (IO.userError message)
private def rejects (r : Except ε α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "conflicting array identity accepted")
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "usage: schema12")
  let document := (← checked (decodeJson (← IO.FS.readFile path))).document
  let runtime ← checked ((RuntimeMetadata.ofDocument document).mapError toString)
  let initial ← checked (create document)
  let arrays ← checked ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let byte := document.queries.primitives.u8
  let child ← checked ((runtime.lookup byte).mapError toString)
  let some node := document.types[byte]? | throw (IO.userError "u8 source absent")
  let some row := document.layouts[node.layoutId]? | throw (IO.userError "u8 layout absent")
  let fields := Array.replicate (document.types.size+3) row
  let aggregate ← checked (SourceLayouts.scalarAggregateLayout runtime.target fields true)
  let (grown,newType) ← checked (internType initial (.tuple (fields.map fun _ => byte)) aggregate "source demand")
  check (newType == arrays.nextId) "fixture did not reproduce the shared frontier"
  let count := UInt64.ofNat (document.types.size+101)
  let (legacy,_) ← checked ((RuntimeArrayTypes.internElement arrays byte count).mapError reprStr)
  check (legacy.ty == newType) "legacy independent allocator did not reproduce collision"
  let attached ← checked (SourceCompilerArrays.view arrays grown)
  rejects (RuntimeArrayTypes.internElement attached byte count)
  let (_,badCache) ← checked ((RuntimeArrayTypes.internElement arrays byte count).mapError reprStr)
  rejects (SourceCompilerArrays.view badCache grown)
  let (actual,cache,world) ← checked (SourceCompilerArrays.internCached attached grown byte count)
  check (actual.ty != newType) "canonical array aliased the new source tuple"
  let expected ← checked ((RuntimeArrayTypes.calculate runtime.target child.layout count).mapError reprStr)
  check (actual.layout == expected) "canonical array full layout differs"
  let (again,cache',world') ← checked (SourceCompilerArrays.internCached cache world byte count)
  check (again == actual && cache'.nextId == cache.nextId && world'.canonical.types.size == world.canonical.types.size)
    "repeated canonical array demand allocated a new identity"
  let some array := world.canonical.types[actual.ty]? | throw (IO.userError "canonical array row absent")
  match array.shape with
  | .array element _ constructor => check (element == byte && constructor.count == count.toNat) "canonical array key differs"
  | _ => throw (IO.userError "canonical array type shape differs")
  check (array.compilerFacts.isNone && world.canonical.instances.size == initial.canonical.instances.size &&
    world.canonical.allocations.size == initial.canonical.allocations.size) "array demand fabricated other compiler capabilities"
  IO.println "PASS actual allocator collision reproduced; common canonical IDs, full layout, idempotence and fail-closed stale cache"
