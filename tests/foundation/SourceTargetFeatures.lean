import Miri.Frontend.FoundationSourceAbi
import Miri.Input.CompilerTargetFeatures
open Lean Miri Miri.Frontend.Foundation Miri.Interpreter
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .ok _ => throw (IO.userError "unknown target-feature evidence accepted") | .error _ => pure ()
private def replace (value : Json) (key : String) (next : Json) : Except String Json := do
  return Json.mkObj ((← value.getObj?).toArray.toList.filter (·.1 != key) ++ [(key,next)])
private def featureResult (features : Array ExecutionCallLeaves.TargetFeature) (available : Array String) (wasm : Bool) :=
  let hooks : ExecutionCallLeaves.TargetFeatures Unit := {
    required := fun _ => pure features
    available := fun name => pure (available.contains name)
    isLikeWasm := pure wasm }
  ExecutionCallLeaves.checkTargetFeatures hooks 0 ()
def main (paths : List String) : IO Unit := do
  let [sourcePath,referencePath] := paths | throw (IO.userError "expected genuine source and schema12 reference")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile sourcePath))))
  let material ← checked (SourceAbiParser.material document)
  let reference ← checked (Json.parse (← IO.FS.readFile referencePath))
  let instances ← checked (reference.getObjValAs? (Array Json) "instances")
  let definitions ← checked (reference.getObjValAs? (Array Json) "definitions")
  let queries ← checked ((← checked (reference.getObjVal? "compiler_runtime_queries")).getObjValAs? (Array Json) "instances")
  let session ← checked (document.source.getObjVal? "session")
  let available ← checked (session.getObjValAs? (Array String) "internal_target_features")
  let referenceSession ← checked (reference.getObjVal? "compiler_session_queries")
  unless available == (← checked (referenceSession.getObjValAs? (Array String) "internal_target_features")) do
    throw (IO.userError "finite session target-feature set differs from compiler")
  for name in #["enabled","forced","plain"] do
    let [selectedInstance] := (instances.filter fun row => (row.getObjValAs? String "def_path").toOption == some name).toList
      | throw (IO.userError "compiler feature instance absent")
    let referenceDefinition ← checked (selectedInstance.getObjValAs? Nat "def_id")
    let some definition := definitions[referenceDefinition]? | throw (IO.userError "compiler raw definition absent")
    let raw : Input.DefinitionId := ⟨← checked (definition.getObjValAs? Nat "crate"),← checked (definition.getObjValAs? Nat "index")⟩
    let actual ← checked (Input.CompilerTargetFeatures.requiredOfDefinition material raw)
    let id ← checked (selectedInstance.getObjValAs? Nat "instance_id")
    let [query] := (queries.filter fun row => (row.getObjValAs? Nat "instance_id").toOption == some id).toList
      | throw (IO.userError "compiler feature evidence absent")
    let expected ← (← checked (query.getObjValAs? (Array Json) "target_features")).mapM fun feature => do
      return (← checked (feature.getObjValAs? String "name"),(← checked (feature.getObjValAs? String "kind")) == "implied")
    unless actual.map (fun feature => (feature.name,feature.implied)) == expected do
      throw (IO.userError "ordered source target-feature list/kind differs from independent compiler")
    let [declaration] := (material.targetFeatureDeclarations.filter (·.definition == raw)).toList
      | throw (IO.userError "typed feature declaration absent")
    let fullKinds ← declaration.features.mapM fun feature => do
      let kind ← match feature.kind with
        | .enabled => pure "enabled" | .forced => pure "forced" | .implied => pure "implied"
        | .unsupported _ => throw (IO.userError "unexpected unsupported compiler kind")
      return (feature.name,kind)
    let oracleKinds ← (← checked (query.getObjValAs? (Array Json) "target_features")).mapM fun feature => do
      return (← checked (feature.getObjValAs? String "name"),← checked (feature.getObjValAs? String "kind"))
    unless fullKinds == oracleKinds do throw (IO.userError "Enabled/Forced distinction was lost")
    if name == "plain" then
      match featureResult actual available false with
      | .ok () () => pure ()
      | _ => throw (IO.userError "known-empty source feature list rejected")
    else
      let message := "calling a function that requires unavailable target features: avx2"
      match featureResult actual available false with
      | .error (.undefinedBehavior reason) () => unless reason == message do throw (IO.userError "feature diagnostic includes implied/misses explicit")
      | _ => throw (IO.userError "unavailable source feature did not produce fixed UB")
      match featureResult actual available true with
      | .error (.termination (.abort reason)) () => unless reason == message do throw (IO.userError "wasm feature abort diagnostic differs")
      | _ => throw (IO.userError "wasm unavailable feature did not abort")
      let unknown := {material with targetFeatureDeclarations := material.targetFeatureDeclarations.map fun row =>
        if row.definition == raw then {row with features := #[⟨"avx2",.unsupported "future"⟩]} else row}
      rejects (Input.CompilerTargetFeatures.requiredOfDefinition unknown raw)
  rejects (Input.CompilerTargetFeatures.requiredOfDefinition {material with targetFeatureDeclarations := #[]} ⟨0,0⟩)
  let some body := document.bodies[0]? | throw (IO.userError "feature body absent")
  let runtime ← checked (replace (← checked (body.getObjVal? "runtime_source")) "target_features" (toJson (#[] : Array Json)))
  let changed ← checked (replace body "runtime_source" runtime)
  let headers ← checked (document.source.getObjValAs? (Array Json) "source_function_signatures")
  let changed ← checked (replace document.source "source_function_signatures" (toJson (headers.push changed)))
  rejects (SourceAbiParser.material (← checked (decode changed)))
  IO.println "ordered Enabled/Forced/Implied features match compiler; fixed UB/abort and missing/unknown/contradictory evidence controls pass"
