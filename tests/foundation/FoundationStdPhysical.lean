import Miri.Frontend.FoundationSignatureFnAbi
import Miri.Frontend.FoundationSignatureFnAbi
import Miri.Input.TableTail
open Lean Miri Miri.Frontend.Foundation
private def expect (r : Except String α) : IO α := match r with
| .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "unsupported aggregate accepted")
def main (paths : List String) : IO Unit := do
  let [sourcePath, oraclePath, closureSourcePath] := paths | throw (IO.userError "usage: source projected-oracle")
  let d ← expect (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let oracle ← expect (Json.parse (← IO.FS.readFile oraclePath))
  check ((← expect (oracle.getObjValAs? String "rustc_commit")) == "8144389c895da997dbdecaa635e41d6a50be6ffd") "oracle compiler revision"
  let expected ← expect (oracle.getObjValAs? (Array Json) "local_layouts")
  let some body := d.bodies[0]? | throw (IO.userError "std body absent")
  let definition ← expect (body.getObjValAs? Nat "definition")
  let localTypes ← expect ((← expect (body.getObjValAs? (Array Nat) "locals")).mapM fun id => do
    eraseRegions (← instantiate #[] #[] (← typeExpr d id)))
  check (localTypes.size == expected.size && expected.size == 7) "std local coverage"
  let target ← expect (runtimeTargetOfTarget d.target)
  let mut registry := PhysicalTypeRegistry.start d
  for (ty,i) in localTypes.zipIdx do
    let (r,id) ← expect (registry.intern ty)
    registry := r
    let actual ← expect (r.runtimeLayout id)
    let some row := expected[i]? | throw (IO.userError "compiler local layout absent")
    let layout ← expect (Input.JsonReader.run Input.DecoderValues.decodeCompilerLayout row.compress)
    let compiler ← expect ((Input.RuntimeMetadata.layout target layout).mapError toString)
    check (actual.layout == compiler) s!"complete real std local{i} layout differs"
  let _ ← expect (rustFunctionAbiOfSourceSignature d definition #[])
  -- The same tuple's MaybeUnsized tail must not use the closure's AlwaysSized
  -- ordering or seed. Inspect its exact independently emitted compiler row in
  -- the closure source test separately; here check the pinned distinction.
  let some (ConcreteType.closure closureDefinition args) := localTypes[6]? | throw (IO.userError "std capture closure absent")
  let some (ConcreteType.tuple fields) := args.back? | throw (IO.userError "capture tuple absent")
  let tuple ← expect (physicalLayoutOfDocument d (.tuple fields))
  let closure ← expect (physicalLayoutOfDocument d (.closure closureDefinition args))
  let tupleOracle ← expect (oracle.getObjVal? "capture_tuple_layout")
  let tupleExpected ← expect (Input.JsonReader.run Input.DecoderValues.decodeCompilerLayout tupleOracle.compress)
  let tupleActual ← expect ((Input.RuntimeMetadata.layout target tuple).mapError toString)
  let tupleExpected ← expect ((Input.RuntimeMetadata.layout target tupleExpected).mapError toString)
  check (tupleActual == tupleExpected) "complete MaybeUnsized capture tuple layout differs"
  check (tuple.randomizationSeed != closure.randomizationSeed) "tuple tail seed accidentally included"
  rejects (physicalLayoutOfDocument d (.tuple (fields.extract 0 2)))
  rejects (physicalLayoutOfDocument d (.tuple #[.tuple #[], .primitive "uint" "u8", .primitive "uint" "u8"]))
  let closureSource ← expect (Json.parse (← IO.FS.readFile closureSourcePath) >>= decode)
  let wrappers ← expect (oracle.getObjValAs? (Array Json) "scalar_wrappers")
  check (wrappers.size == 2) "compiler scalar wrapper coverage"
  for wrapper in wrappers do
    let defn ← expect (wrapper.getObjVal? "definition")
    let crate ← expect (defn.getObjValAs? Nat "crate")
    let index ← expect (defn.getObjValAs? Nat "index")
    let some sourceDef := closureSource.definitions.findIdx? (fun row =>
      (row.getObjValAs? Nat "crate_index").toOption == some crate &&
      (row.getObjValAs? Nat "index").toOption == some index)
      | throw (IO.userError "source scalar wrapper declaration absent")
    let (r,id) ← expect ((PhysicalTypeRegistry.start closureSource).intern (.nominal sourceDef #[]))
    let actual ← expect (r.runtimeLayout id)
    let expected ← expect (wrapper.getObjVal? "layout")
    let expected ← expect (Input.JsonReader.run Input.DecoderValues.decodeCompilerLayout expected.compress)
    let expected ← expect ((Input.RuntimeMetadata.layout target expected).mapError toString)
    check (actual.layout == expected) "complete source scalar wrapper differs"
  let methodMode ← expect (oracle.getObjVal? "exitcode_method_mode")
  let methodDef ← expect (methodMode.getObjVal? "definition")
  let crate ← expect (methodDef.getObjValAs? Nat "crate")
  let index ← expect (methodDef.getObjValAs? Nat "index")
  let some defId := closureSource.definitions.findIdx? (fun row =>
    (row.getObjValAs? Nat "crate_index").toOption == some crate &&
    (row.getObjValAs? Nat "index").toOption == some index)
    | throw (IO.userError "method argument source declaration absent")
  let expectedMode ← expect (methodMode.getObjVal? "mode")
  let expectedMode ← expect (Input.JsonReader.run (Input.DecoderValues.parseAbiPassMode "$.mode") expectedMode.compress)
  let actualMode ← expect (rustPassModeOfDocument closureSource false (.nominal defId #[]))
  check (actualMode == expectedMode) "complete std ExitCode::to_i32 argument pass-mode differs"
  rejects (rustPassMode closureSource.target closureSource.target.architecture false (.nominal defId #[]))
  rejects (rustPassModeOfDocument { closureSource with target := { closureSource.target with architecture := "aarch64" } }
    false (.nominal defId #[]))
  let some result := localTypes[5]? | throw (IO.userError "Result source absent")
  rejects (rustPassModeOfDocument d false result)
  let methodDefinition ← expect (oracle.getObjVal? "method_definition")
  let methodCrate ← expect (methodDefinition.getObjValAs? Nat "crate")
  let methodIndex ← expect (methodDefinition.getObjValAs? Nat "index")
  let some methodId := closureSource.definitions.findIdx? (fun row =>
    (row.getObjValAs? Nat "crate_index").toOption == some methodCrate &&
    (row.getObjValAs? Nat "index").toOption == some methodIndex)
    | throw (IO.userError "inherent method source definition absent")
  let (methodRegistry, fullAbi) ← expect (rustFunctionAbiOfSourceSignature closureSource methodId #[])
  let expectedAbi ← expect (oracle.getObjVal? "exitcode_method_abi")
  let expectedAbi ← expect (Input.JsonReader.run Input.DecoderValues.decodeCompilerFunctionAbi expectedAbi.compress)
  check (fullAbi.arguments.size == 1 && expectedAbi.arguments.size == 1) "inherent method argument count"
  let some argument := fullAbi.arguments[0]? | throw (IO.userError "method argument absent")
  let (argumentNode, _) ← expect (methodRegistry.lookup argument.typeId)
  let .adt argumentShape := argumentNode.shape | throw (IO.userError "method argument not nominal")
  check (argumentShape.definition == defId) "method argument declaration identity"
  let (returnNode, _) ← expect (methodRegistry.lookup fullAbi.returnValue.typeId)
  let .int (.known .i32) := returnNode.shape | throw (IO.userError "method output not exact i32")
  let returnShape ← expect (oracle.getObjVal? "method_return_shape")
  check ((← expect (returnShape.getObjValAs? String "kind")) == "int" &&
    (← expect (returnShape.getObjValAs? String "signed_kind")) == "i32") "compiler method output identity"
  let returnLayout ← expect (methodRegistry.runtimeLayout fullAbi.returnValue.typeId)
  let compilerReturn ← expect (oracle.getObjVal? "method_return_layout")
  let compilerReturn ← expect (Input.JsonReader.run Input.DecoderValues.decodeCompilerLayout compilerReturn.compress)
  let compilerReturn ← expect ((Input.RuntimeMetadata.layout target compilerReturn).mapError toString)
  check (returnLayout.layout == compilerReturn) "complete method return layout differs"
  let rebase (a b : Input.AbiArgument) := {a with typeId := b.typeId, layoutId := b.layoutId}
  let rebased := { fullAbi with
    arguments := (fullAbi.arguments.zip expectedAbi.arguments).map fun (a,b) => rebase a b
    returnValue := rebase fullAbi.returnValue expectedAbi.returnValue }
  check (rebased == expectedAbi) "complete inherent method FnAbi differs"
  rejects (rustFunctionAbiOfSourceSignature { closureSource with source := (closureSource.source.setObjVal! "source_function_signatures" (.arr #[])) } methodId #[])
  IO.println "PASS actual std source locals, all7 complete local layouts, direct root FnAbi, both source ExitCode wrappers/full inherent FnAbi; unsupported aggregate controls"
