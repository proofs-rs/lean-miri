import Miri.Frontend.FoundationObligations
open Lean Miri.Frontend.Foundation
private def checked {α : Type} (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def failure {α : Type} (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "invalid generic source layers accepted")
def main (paths : List String) : IO Unit := do
  let [path,compilerPath] := paths | throw (IO.userError "expected finite/compiler inherited fixtures")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let [body] := document.bodies.toList | throw (IO.userError "expected one inherited template")
  let source ← checked (body.getObjVal? "environment")
  let flat ← checked (flattenEnvironment document source)
  let layers ← checked (source.getObjValAs? (Array Json) "layers")
  let [impl,method] := layers.toList | throw (IO.userError "lexical impl/method layers absent")
  let parameters ← checked (flat.getObjValAs? (Array Json) "parameters")
  let [first,second] := parameters.toList | throw (IO.userError "inherited own args lost")
  unless (← checked (first.getObjValAs? Nat "index")) == 0 &&
      (← checked (second.getObjValAs? Nat "index")) == 1 do throw (IO.userError "original indices changed")
  let some selfType ← checked (impl.getObjValAs? (Option Nat) "self_type")
    | throw (IO.userError "impl self-type source link absent")
  let some selfRow := document.types[selfType]? | throw (IO.userError "impl self-type row absent")
  unless (← checked ((← checked (selfRow.getObjVal? "shape")).getObjValAs? String "kind")) == "adt" do
    throw (IO.userError "impl self-type ADT source lost")
  let arguments := #[some (.primitive "uint" "u8"),some (.primitive "uint" "u16")]
  let _ ← checked (checkEnvironment document arguments #[none,none] source)
  let locals ← checked (body.getObjValAs? (Array Nat) "locals")
  let some returnType := locals[0]? | throw (IO.userError "return type source absent")
  let output ← checked (instantiate arguments #[none,none] (← checked (typeExpr document returnType)))
  unless sameConcrete 1024 output (.primitive "uint" "u16") do throw (IO.userError "child index did not substitute u16")
  let compiler ← checked (Json.parse (← IO.FS.readFile compilerPath))
  let instances ← checked (compiler.getObjValAs? (Array Json) "instances")
  let some actual := instances.find? (fun row => (row.getObjValAs? String "def_path").toOption == some "Carrier::<T>::identity")
    | throw (IO.userError "compiler inherited instance absent")
  let args ← checked (actual.getObjValAs? (Array Json) "generic_args")
  let types ← checked (compiler.getObjValAs? (Array Json) "types")
  unless args.size == 2 do throw (IO.userError "compiler inherited argument count differs")
  for (argument,expected) in args.zip #["u8","u16"] do
    let type ← checked (argument.getObjValAs? Nat "value")
    let some row := types[type]? | throw (IO.userError "compiler argument type absent")
    unless (← checked (row.getObjValAs? String "display")) == expected do throw (IO.userError "compiler inherited order differs")
  failure (checkEnvironment document #[some (.primitive "uint" "u16")] #[none] source)
  for bad in #[#[], #[method], layers.reverse,
      #[impl,method.setObjVal! "parent_count" (toJson (0 : Nat))],
      #[impl,method.setObjVal! "self_type" (toJson selfType)]] do
    failure (flattenEnvironment document (source.setObjVal! "layers" (toJson bad)))
  let missingParent := Json.mkObj [("owner",← checked (impl.getObjVal? "owner")),
    ("parent_count",← checked (impl.getObjVal? "parent_count")),("self_type",← checked (impl.getObjVal? "self_type")),
    ("parameters",← checked (impl.getObjVal? "parameters")),("clauses",← checked (impl.getObjVal? "clauses"))]
  failure (flattenEnvironment document (source.setObjVal! "layers" (toJson #[missingParent,method])))
  failure (flattenEnvironment document flat)
  IO.println "generic layers: real impl→method and separate ADT self link retain indices; pure u8/u16 substitution matches compiler; missing/extra/reordered layers, counts/links/fields, old flat source reject"
