import Miri.Frontend.FoundationSignatureBinder
open Lean Miri.Frontend.Foundation
private def checked {α : Type} (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected signature callback source")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let some body := document.bodies[0]? | throw (IO.userError "source body missing")
  let signature ← checked (body.getObjVal? "signature")
  let erased ← checked (eraseSignatureBinder document signature)
  let inputs ← checked (signature.getObjValAs? (Array Nat) "inputs")
  let [reference,callback] := inputs.toList | throw (IO.userError "callback fixture inputs missing")
  let .functionPointer #[.primitive "uint" "u8"] (.primitive "uint" "u8") "safe" "rust" false ←
      checked (instantiate #[] #[] (← checked (typeExpr erased callback)))
    | throw (IO.userError "noncapturing inner callback changed")
  let some row := document.types[callback]? | throw (IO.userError "callback source row absent")
  let shape ← checked (row.getObjVal? "shape")
  let inner ← checked (shape.getObjVal? "signature")
  let broken := row.setObjVal! "shape" (shape.setObjVal! "signature"
    (inner.setObjVal! "inputs" (toJson #[reference])))
  let mutated := { document with types := document.types.mapIdx fun index source => if index == callback then broken else source }
  match eraseSignatureBinder mutated signature with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "inner empty binder captured outer lifetime")
  IO.println "foundation signature callback: outer named binder erases; noncapturing empty FnPtr binder retained; outer-region capture rejects"
