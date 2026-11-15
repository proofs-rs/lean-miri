import Miri.Frontend.FoundationGenericEnvironment
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .ok _ => throw (IO.userError "invalid implicit Self witness accepted") | .error _ => pure ()
private def replace (value : Json) (key : String) (next : Json) : Except String Json := do
  let fields ← value.getObj?
  return Json.mkObj ((fields.toArray.toList.filter (·.1 != key)) ++ [(key,next)])
private def remove (value : Json) (key : String) : Except String Json := do
  return Json.mkObj ((← value.getObj?).toArray.toList.filter (·.1 != key))
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine implicit Self source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let headers ← checked (document.source.getObjValAs? (Array Json) "source_function_signatures")
  let mut observed := 0
  for header in headers do
    let environment ← checked (header.getObjVal? "environment")
    let layers ← checked (environment.getObjValAs? (Array Json) "layers")
    for index in [:layers.size] do
      let some layer := layers[index]? | throw (IO.userError "source layer absent")
      let owner ← checked (layer.getObjValAs? Nat "owner")
      let some row := document.definitions[owner]? | throw (IO.userError "source owner absent")
      if (← checked (row.getObjValAs? String "kind")) == "Trait" then
        observed := observed + 1
        let flat ← checked (flattenEnvironment document environment)
        let parameters ← checked (flat.getObjValAs? (Array Json) "parameters")
        let some self := parameters[0]? | throw (IO.userError "trait Self slot absent")
        unless (← checked (self.getObjValAs? Nat "definition")) == owner &&
            (← checked (self.getObjValAs? Nat "index")) == 0 do
          throw (IO.userError "raw trait Self identity/index changed")
        if h : index < layers.size then
          let changedLayer ← checked (replace layer "has_self" (toJson false))
          let changedEnv ← checked (replace environment "layers" (toJson (layers.set index changedLayer h)))
          rejects (flattenEnvironment document changedEnv)
          let missing ← checked (remove layer "has_self")
          rejects (flattenEnvironment document (← checked (replace environment "layers" (toJson (layers.set index missing h)))))
          let declaration ← checked (row.getObjVal? "generic_declaration")
          let declaration ← checked (replace declaration "has_self" (toJson false))
          let changedRow ← checked (replace row "generic_declaration" declaration)
          if hd : owner < document.definitions.size then
            let changed := {document with definitions := document.definitions.set owner changedRow hd}
            rejects (flattenEnvironment changed changedEnv)
          else throw (IO.userError "owner definition absent")
        else throw (IO.userError "layer index absent")
  unless observed > 0 do throw (IO.userError "genuine implicit trait Self header absent")
  -- Required grammar also applies to ordinary zero-slot owners: removing both
  -- redundant source witnesses must not silently activate an old-schema path.
  let some body := document.bodies[0]? | throw (IO.userError "ordinary body absent")
  let environment ← checked (body.getObjVal? "environment")
  let layers ← checked (environment.getObjValAs? (Array Json) "layers")
  let some layer := layers[0]? | throw (IO.userError "ordinary layer absent")
  let owner ← checked (layer.getObjValAs? Nat "owner")
  let some row := document.definitions[owner]? | throw (IO.userError "ordinary owner absent")
  let declaration ← checked (remove (← checked (row.getObjVal? "generic_declaration")) "has_self")
  let row ← checked (replace row "generic_declaration" declaration)
  let layer ← checked (remove layer "has_self")
  if h : 0 < layers.size then
    let environment ← checked (replace environment "layers" (toJson (layers.set 0 layer h)))
    if hd : owner < document.definitions.size then
      let changed := {document with definitions := document.definitions.set owner row hd}
      rejects (flattenEnvironment changed environment)
    else throw (IO.userError "ordinary owner index absent")
  else throw (IO.userError "ordinary layer index absent")
  IO.println "genuine implicit Self preserves raw owner identity; false/missing declaration-layer witnesses reject"
