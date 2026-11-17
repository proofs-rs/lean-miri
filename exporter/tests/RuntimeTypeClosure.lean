import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata
import Miri.Input.ConcreteVTable

open Miri.Input

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [path, late, ty1, principal1, slot1, instance1, ty2, principal2, slot2, instance2] := args
    | throw (IO.userError "expected input, type, and two vtable bindings")
  let values ← [late, ty1, principal1, slot1, instance1, ty2, principal2, slot2, instance2].mapM fun value =>
    match value.toNat? with
    | some value => pure value
    | none => throw (IO.userError "invalid numeric argument")
  let [late, ty1, principal1, slot1, instance1, ty2, principal2, slot2, instance2] := values
    | throw (IO.userError "invalid argument count")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let layout ← must ((runtime.lookup late).mapError toString)
  unless layout.ty == late do throw (IO.userError "LateOnly layout changed its type identity")
  for (ty, principal, slot, expected) in [(ty1, principal1, slot1, instance1),
                                           (ty2, principal2, slot2, instance2)] do
    let entries ← must (ConcreteVTable.entries decoded.document (some principal) ty)
    match entries[slot]? with
    | some (.method actual) =>
      unless actual == expected do throw (IO.userError "vtable slot resolved to the wrong method")
    | _ => throw (IO.userError "virtual method missing from its vtable slot")
  IO.println "LateOnly runtime layout and both exact vtable slots resolved"
