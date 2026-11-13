import Miri.Input.Decoder
import Miri.Input.CallResolution

open Lean Miri.Input Miri.ABI
private def must (value : Except String A) : IO A :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def number (value : String) : IO Nat :=
  match value.toNat? with | some result => pure result | none => throw (IO.userError "expected explicit source ID")

def main (args : List String) : IO Unit := do
  let [path,layoutText,typeText,abiText] := args
    | throw (IO.userError "expected source document, exact LayoutId, TypeId and FnAbiId")
  let layoutId ← number layoutText
  let ty ← number typeText
  let abiId ← number abiText
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let some source := document.types[ty]? | throw (IO.userError "source type absent")
  let child ← match source.shape with
    | .reference child .. | .rawPointer child _ => pure child
    | _ => throw (IO.userError "selected source type is not a pointer")
  let some pointee := document.types[child]? | throw (IO.userError "source pointee absent")
  let .dynamicTraitObject .. := pointee.shape | throw (IO.userError "selected source pointer is not fat Dynamic")
  let some seed := document.layouts[layoutId]? | throw (IO.userError "source layout absent")
  check (seed.pointerType == some ty) "selected seed is not the exact canonical pointer recipe"
  let some checked := runtime.checkedMaterial | throw (IO.userError "checked source materialWorld absent")
  let materialWorld := TypeArena.World.ofCheckedMaterial checked
  let original ← must (GenericInstantiationWorld.ofType materialWorld 16384 ty)
  let (canonical,after) ← must ((RuntimeMetadata.layoutInWorld runtime ty).run materialWorld)
  check (canonical.ty == ty && canonical.layout.size.bytes.toNat == 2 * runtime.target.pointerSize.bytes.toNat)
    "canonical Dynamic pointer is not two target pointers"
  let .ScalarPair .. := canonical.layout.backendRepr
    | throw (IO.userError "canonical Dynamic pointer lost its two source scalars")
  check (after.constructedTypes.size > materialWorld.constructedTypes.size)
    "regression did not exercise execution-owned metadata field construction"
  check ((← must (GenericInstantiationWorld.ofType after 16384 ty)) == original)
    "contextual layout changed the original source type identity"
  let physical ← must ((runtime.layoutById layoutId).mapError toString)
  check (physical == canonical.layout) "contextual physical adapter differs from complete World layout"
  -- Import the actual source ABI, not a fabricated argument or TypeId placeholder.
  let abi ← must (CallResolution.functionAbiId runtime abiId)
  let mut matching := 0
  for argument in abi.args.push abi.ret do
    check (argument.layout.ty < materialWorld.materialTypes.size) "intermediate metadata type ID escaped physical ABI import"
    let _ ← must (GenericInstantiationWorld.ofType materialWorld 16384 argument.layout.ty)
    if argument.layout.ty == ty then
      check (argument.layout.layout == physical) "source ABI uses a different contextual layout"
      matching := matching + 1
  check (matching > 0) "selected ABI did not exercise the requested source pointer seed"
  match RuntimeMetadata.resolveLayout runtime.target document.types document.layouts layoutId
      document.definitions document.typeConstants document.predicates with
  | .error (.unsupported "raw metadata fields need source normalization") => pure ()
  | _ => throw (IO.userError "bare context-free adapter lost its exact source-context residual")
  IO.println s!"PASS exact layout {layoutId}/type {ty}/ABI {abiId}: complete fat pointer layout matches contextual World; canonical metadata constructs {after.constructedTypes.size} types; imported ABI roots remain in original materialWorld; bare adapter rejects absent normalization"
