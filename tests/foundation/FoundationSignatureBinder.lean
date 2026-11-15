import Miri.Frontend.FoundationRegionErasure
import Miri.Frontend.FoundationTypeRegistry
import Miri.Frontend.FoundationSignatureBinder
import Miri.Input.Decoder

open Lean Miri Miri.Frontend.Foundation

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

/-- Compare a retained named FnSig binder with a fresh compiler FnPtr, then
check strict pure erasure and rejection of escaping/mismatched source regions.
This does not add a general bound-type, const or nested-binder solver. -/
def main (paths : List String) : IO Unit := do
  let [finitePath, compilerPath] := paths | throw (IO.userError "expected finite and ordinary binder exports")
  let document ← checked (Json.parse (← IO.FS.readFile finitePath) >>= decode)
  let some body := document.bodies[0]? | throw (IO.userError "source body absent")
  let signature ← checked (body.getObjVal? "signature")
  let variables ← checked (signatureBoundVariables document signature)
  let [MIR.BoundVariableKind.Region (.Named sourceNamed)] := variables.toList
    | throw (IO.userError "fixture named lifetime binder absent")
  let inputs ← checked (signature.getObjValAs? (Array Nat) "inputs")
  let some input := inputs[0]? | throw (IO.userError "source signature input absent")
  match typeExpr document input with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "bound source reference escaped signature binder")
  let erased ← checked (eraseSignatureBinder document signature)
  unless erased.source == document.source && erased.types.size == document.types.size do
    throw (IO.userError "binder erasure changed original source or type indices")
  let ty ← checked (instantiate #[] #[] (← checked (typeExpr erased input)))
  unless sameConcrete 1024 ty (.pointer "reference_erased_const" (.primitive "uint" "u8")) do
    throw (IO.userError "known bound reference did not erase exactly")
  let locals ← checked ((← checked (body.getObjValAs? (Array Nat) "locals")).mapM fun id => do
    eraseRegions (← instantiate #[] #[] (← typeExpr document id)))
  unless locals.all (sameConcrete 1024 ty) do
    throw (IO.userError "signature/body erasure join changed")
  let compiler ← checked (Input.decodeJson (← IO.FS.readFile compilerPath))
  let doc := compiler.document
  let some root := doc.bodyRoots[0]? | throw (IO.userError "compiler root absent")
  let some mainEntry := doc.queries.main.entries.find? (·.definition == root.definitionId)
    | throw (IO.userError "compiler source signature entry absent")
  let some pointer := doc.types[mainEntry.signature.functionPointerType]?
    | throw (IO.userError "compiler signature FnPtr type absent")
  let .functionPointer actualSignature actualVariables := pointer.shape
    | throw (IO.userError "compiler signature type is not FnPtr")
  let [MIR.BoundVariableKind.Region (.Named actualNamed)] := actualVariables.toList
    | throw (IO.userError "compiler source bound lifetime identity absent")
  let some sourceRow := document.definitions[sourceNamed]? | throw (IO.userError "source bound definition absent")
  let some actualRow := doc.definitions[actualNamed]? | throw (IO.userError "compiler bound definition absent")
  unless actualRow.crateIndex == (← checked (sourceRow.getObjValAs? Nat "crate_index")) &&
      actualRow.index == (← checked (sourceRow.getObjValAs? Nat "index")) &&
      mainEntry.signature.hasBoundVariables && mainEntry.signature.outputHasBoundVariables &&
      actualSignature.inputs.size == 1 && actualSignature.safety == .Safe &&
      actualSignature.abi == .Rust && !actualSignature.cVariadic do
    throw (IO.userError "retained source signature binder differs from compiler")
  let some row := document.types[input]? | throw (IO.userError "source reference row absent")
  let shape ← checked (row.getObjVal? "shape")
  let region ← checked (shape.getObjVal? "region")
  for (brokenRegion, expected) in #[(region.setObjVal! "debruijn" (toJson (1 : Nat)),
      "escaping/nested signature bound region unsupported"),
      (region.setObjVal! "variable" (toJson (1 : Nat)), "signature bound region variable absent"),
      (region.setObjVal! "region_kind" (Json.mkObj [("kind", toJson "anonymous")]), "signature bound region identity mismatch")] do
    let brokenRow := row.setObjVal! "shape" (shape.setObjVal! "region" brokenRegion)
    let malformed := { document with types := document.types.mapIdx fun i original =>
      if i == input then brokenRow else original }
    match eraseSignatureBinder malformed signature with
    | .error error => unless error == expected do throw (IO.userError s!"unexpected binder diagnostic: {error}")
    | .ok _ => throw (IO.userError "invalid signature region erased")
  let typeBinder := signature.setObjVal! "bound_variables" (toJson #[Json.mkObj [("kind", toJson "type")]])
  match eraseSignatureBinder document typeBinder with
  | .error "signature type/const binder unsupported" => pure ()
  | _ => throw (IO.userError "unhandled type binder erased")
  match eraseSignatureBinder document (signature.setObjVal! "bound_variables" Json.null) with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "missing signature binder material became empty")
  IO.println "foundation FnSig binder: named source identity matches compiler; pure erased reference/body join and five malformed binder controls pass"
