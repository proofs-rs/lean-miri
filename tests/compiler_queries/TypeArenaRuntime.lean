import Miri.Input.Decoder
import Miri.Input.RuntimeArrayTypes

open Lean Miri.Input Miri.ABI
private def must (value : Except String A) : IO A :=
  match value with | .ok v => pure v | .error e => throw (IO.userError e)
private def metadata (value : Except RuntimeMetadataError A) : IO A :=
  must (value.mapError toString)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

-- Fresh producer input supplies the target and exact primitive identities.
def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "expected fresh export path")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let runtime ← metadata (RuntimeMetadata.ofDocument decoded.document)
  let world ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let u8 := runtime.source.queries.primitives.u8
  let (arrayLayout,world) ← must ((RuntimeArrayTypes.internElement world u8 7).mapError reprStr)
  let array := arrayLayout.ty
  let (pointer,world) ← must ((RuntimeArrayTypes.perform world (TypeArena.World.internType (.rawPointer array .Mut))).mapError reprStr)
  let (reference,world) ← must ((RuntimeArrayTypes.perform world (TypeArena.World.internType (.reference pointer .Mut .Erased))).mapError reprStr)
  let (nestedLayout,world) ← must ((RuntimeArrayTypes.internElement world pointer 3).mapError reprStr)
  check (array >= runtime.source.types.size && pointer >= runtime.source.types.size &&
    reference >= runtime.source.types.size && nestedLayout.ty >= runtime.source.types.size)
    "runtime constructor control accidentally reused material nodes"
  let (pointerLayout,world) ← must ((RuntimeArrayTypes.lookup world pointer).mapError reprStr)
  let (referenceLayout,world) ← must ((RuntimeArrayTypes.lookup world reference).mapError reprStr)
  check (arrayLayout.layout.size.bytes == 7) "new byte array layout"
  check (pointerLayout.layout.size == runtime.target.pointerSize) "new pointer to array layout"
  check (referenceLayout.layout.size == pointerLayout.layout.size) "new nested reference layout"
  check (nestedLayout.layout.size.bytes == pointerLayout.layout.size.bytes * 3) "array of new pointers layout"
  let .constructed (.reference child .Mut .Erased) ← must (world.arena.lookupType reference)
    | throw (IO.userError "new reference constructor absent")
  check (child == pointer) "new reference pointee identity"
  let (element,world) ← must ((RuntimeArrayTypes.fieldLayout world nestedLayout.ty 2).mapError reprStr)
  check (element.ty == pointer && element.layout == pointerLayout.layout) "new array field layout"
  let (repeated,world) ← must ((RuntimeArrayTypes.internElement world u8 7).mapError reprStr)
  check (repeated.ty == array) "persistent interner changed canonical identity"
  let .constructed (.array _ constantId) ← must (world.arena.lookupType array)
    | throw (IO.userError "new array constructor absent")
  let constant ← must (world.arena.lookupConstant constantId)
  check (match constant with
    | .Value ty tree => ty == runtime.source.queries.primitives.usize &&
        tree.nodes == #[.Leaf 7 runtime.target.pointerSize.bytes.toNat]
    | _ => false) "new array exact usize constant"
  check (!(runtime.lookup array).isOk) "source-only metadata accepted an execution-owned ID"
  for source in runtime.source.types do
    if source.shapeKind == .str then
      check (!(RuntimeArrayTypes.internElement world source.id 2).isOk) "array of unsized str accepted"
  if runtime.target.base.pointerWidth.bits.toNat < 64 then
    let tooLong := UInt64.ofNat (2^runtime.target.base.pointerWidth.bits.toNat)
    check (!(RuntimeArrayTypes.internElement world u8 tooLong).isOk) "array target-usize overflow accepted"
  IO.println "persistent type universe nested constructors/layouts/identity/constants passed"
