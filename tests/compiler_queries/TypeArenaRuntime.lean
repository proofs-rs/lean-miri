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
  let array ← must (TypeArena.internArray runtime.source.types u8 7)
  let pointer ← must (TypeArena.intern runtime.source.types array false)
  let reference ← must (TypeArena.intern runtime.source.types pointer true)
  let arrayOfPointers ← must (TypeArena.internArray runtime.source.types pointer 3)
  check (array >= runtime.source.types.size && pointer >= runtime.source.types.size &&
    reference >= runtime.source.types.size && arrayOfPointers >= runtime.source.types.size)
    "runtime constructor control accidentally reused material nodes"
  let arrayLayout ← metadata (runtime.lookup array)
  let pointerLayout ← metadata (runtime.lookup pointer)
  let referenceLayout ← metadata (runtime.lookup reference)
  let nestedLayout ← metadata (runtime.lookup arrayOfPointers)
  check (arrayLayout.layout.size.bytes == 7) "new byte array layout"
  check (pointerLayout.layout.size == runtime.target.pointerSize) "new pointer to array layout"
  check (referenceLayout.layout.size == pointerLayout.layout.size) "new nested reference layout"
  check (nestedLayout.layout.size.bytes == pointerLayout.layout.size.bytes * 3) "array of new pointers layout"
  let child ← metadata (runtime.pointee referenceLayout)
  check (child.ty == pointer) "new reference pointee identity"
  let element ← metadata (runtime.field nestedLayout 2)
  check (element.ty == pointer && element.layout == pointerLayout.layout) "new array field layout"
  let (interned, world) ← must ((RuntimeArrayTypes.internElement world u8 7).mapError reprStr)
  let (repeated, _) ← must ((RuntimeArrayTypes.internElement world u8 7).mapError reprStr)
  check (interned.ty == array && repeated.ty == array) "world and lazy arena disagree on canonical identity"
  let source ← metadata (runtime.node array)
  let .array _ constantId _ := source.shape | throw (IO.userError "new array node shape")
  let constant ← metadata (runtime.typeConstant constantId)
  check (match constant with
    | .Value ty tree => ty == runtime.source.queries.primitives.usize &&
        tree.nodes == #[.Leaf 7 runtime.target.pointerSize.bytes.toNat]
    | _ => false) "new array exact usize constant"
  for source in runtime.source.types do
    if source.shapeKind == .str then
      let invalid := TypeArena.arrayId runtime.source.types.size source.id 2
      check (!(runtime.lookup invalid).isOk) "array of unsized str accepted"
  if runtime.target.base.pointerWidth.bits.toNat < 64 then
    let tooLong := UInt64.ofNat (2^runtime.target.base.pointerWidth.bits.toNat)
    check (!(runtime.lookup (TypeArena.arrayId runtime.source.types.size u8 tooLong)).isOk)
      "array target-usize overflow accepted"
  IO.println "lazy type arena nested constructors/layouts/identity/constants passed"
