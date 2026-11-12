import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata
open Miri.Input
private def must {α} [ToString ε] : Except ε α → IO α
  | .ok x => pure x | .error e => throw (IO.userError (toString e))
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh raw canonical overflow document")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let some checked := runtime.checkedMaterial | throw (IO.userError "checked material absent")
  let initial := TypeArena.World.ofCheckedMaterial checked
  let some array := decoded.document.types.find? (fun node => match node.shape with
    | .array _ _ identity => identity.count == 2305843009213693952 | _ => false)
    | throw (IO.userError "oversized source array absent")
  let some pointer := decoded.document.types.find? (fun node => match node.shape with
    | .rawPointer pointee _ => pointee == array.id | _ => false)
    | throw (IO.userError "source pointer absent")
  let (actual,world) ← must ((runtime.layoutInWorld pointer.id).run initial)
  unless actual.layout.size == runtime.target.pointerSize && actual.layout.fields == .Primitive do
    throw (IO.userError "unused oversized pointee affected pointer layout")
  match (runtime.layoutInWorld array.id).run world with
  | .ok _ => throw (IO.userError "oversized array layout demand unexpectedly succeeded")
  | .error error =>
    unless error.contains "bound" do throw (IO.userError s!"wrong explicit array demand error: {error}")
    IO.println s!"PASS pointer layout succeeds without oversized pointee layout; demanded array fails exactly: {error}"
