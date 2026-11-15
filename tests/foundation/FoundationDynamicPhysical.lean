import Miri.Frontend.FoundationPrimitiveFacts
import Miri.Frontend.FoundationSignatureFnAbi
import Miri.Input.Decoder

open Lean Miri Miri.Frontend.Foundation
private def expect (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def rejects (r : Except String α) : IO Unit :=
  match r with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported dyn material accepted")
private def sameLeaf (left right : Input.TypeShape) : Bool :=
  match left, right with
  | .tuple l, .tuple r => l.isEmpty && r.isEmpty
  | .int (.known l), .int (.known r) | .uint (.known l), .uint (.known r) => l == r
  | _, _ => false

def main (paths : List String) : IO Unit := do
  let [sourcePath, referencePath] := paths | throw (IO.userError "usage: FoundationDynamicPhysical FOUNDATION_JSON SCHEMA12_JSON")
  let d ← expect (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let some sourceBody := d.bodies[0]? | throw (IO.userError "dyn source body absent")
  let definition ← expect (sourceBody.getObjValAs? Nat "definition")
  let localTypes ← expect ((← expect (sourceBody.getObjValAs? (Array Nat) "locals")).mapM fun id => do
    eraseRegions (← instantiate #[] #[] (← typeExpr d id)))
  let some ty := localTypes[1]? | throw (IO.userError "dyn argument absent")
  let (r, id) ← expect ((PhysicalTypeRegistry.start d).intern ty)
  let r ← expect (r.withPrimitiveFactsFor (List.range r.types.size).toArray)
  let (node, _) ← expect (r.lookup id)
  let dynId ← match node.shape with
    | .reference id .Not .Erased | .rawPointer id .Not => pure id
    | _ => throw (IO.userError "dyn pointer shape mismatch")
  let (dynNode, _) ← expect (r.lookup dynId)
  let .dynamicTraitObject predicates principal .Erased := dynNode.shape | throw (IO.userError "dynamic object shape mismatch")
  let reference ← expect (Input.decodeJson (← IO.FS.readFile referencePath))
  let reference := reference.document
  let runtime ← expect ((Input.RuntimeMetadata.ofDocument reference).mapError toString)
  let some body := reference.bodies[0]? | throw (IO.userError "reference body absent")
  let some compilerId := body.mir.locals[1]? | throw (IO.userError "reference local absent")
  let compilerNode ← expect ((runtime.node compilerId).mapError toString)
  check (node.shapeKind == compilerNode.shapeKind) "dynamic pointer category differs"
  let compilerDynId ← match compilerNode.shape with
    | .reference id .Not .Erased | .rawPointer id .Not => pure id
    | _ => throw (IO.userError "compiler pointer shape mismatch")
  let compilerDyn ← expect ((runtime.node compilerDynId).mapError toString)
  let .dynamicTraitObject compilerPredicates compilerPrincipal .Erased := compilerDyn.shape
    | throw (IO.userError "compiler dynamic shape mismatch")
  let actual ← expect (r.runtimeLayout id)
  let expected ← expect ((runtime.lookup compilerId).mapError toString)
  check (actual.layout == expected.layout) "complete dyn-reference layout differs"
  let actualDyn ← expect (r.runtimeLayout dynId)
  let expectedDyn ← expect ((runtime.lookup compilerDynId).mapError toString)
  check (actualDyn.layout == expectedDyn.layout) "complete unsized dyn layout differs"
  check (predicates.size == compilerPredicates.size && predicates.size == 4) "existential predicate count"
  check ((principal.bind fun id => predicates.findIdx? (· == id)) ==
    (compilerPrincipal.bind fun id => compilerPredicates.findIdx? (· == id))) "principal predicate join"
  for (leftId, rightId) in predicates.zip compilerPredicates do
    let some left := r.predicates[leftId]? | throw (IO.userError "source predicate missing")
    let some right := reference.predicates[rightId]? | throw (IO.userError "compiler predicate missing")
    check (left.kind == right.kind && left.definitionPath == right.definitionPath &&
      left.boundVariables == right.boundVariables && left.genericArgs.size == right.genericArgs.size)
      "predicate definition/binder fields differ"
    for (leftArg, rightArg) in left.genericArgs.zip right.genericArgs do
      let .Type leftTy := leftArg | throw (IO.userError "source existential arg form")
      let .Type rightTy := rightArg | throw (IO.userError "compiler existential arg form")
      let (a, _) ← expect (r.lookup leftTy)
      let b ← expect ((runtime.node rightTy).mapError toString)
      check (sameLeaf a.shape b.shape) "predicate type argument differs"
    match left.projectionTerm, right.projectionTerm with
    | none, none => pure ()
    | some a, some b =>
      let (a, _) ← expect (r.lookup a)
      let b ← expect ((runtime.node b).mapError toString)
      check (sameLeaf a.shape b.shape) "projection term type differs"
    | _, _ => throw (IO.userError "projection term optional mismatch")
  let some facts := dynNode.compilerFacts | throw (IO.userError "structural dyn facts absent")
  let some compilerFacts := compilerDyn.compilerFacts | throw (IO.userError "compiler dyn facts absent")
  for query in facts.booleanQueries do
    check (compilerFacts.booleanQueries.contains query) s!"dyn compiler leaf differs: {query.1}"
  for (name, value) in facts.typeQueries do
    let some (_, compilerValue) := compilerFacts.typeQueries.find? (·.1 == name)
      | throw (IO.userError "compiler dynamic type query absent")
    if name == "normalized" || name == "metadata_tail" then
      check (value == some dynId && compilerValue == some compilerDynId) "dynamic normalized identity differs"
    else
      match value, compilerValue with
      | none, none => pure ()
      | some a, some b =>
        let (a, _) ← expect (r.lookup a)
        let b ← expect ((runtime.node b).mapError toString)
        check (sameLeaf a.shape b.shape) "dynamic type query result differs"
      | _, _ => throw (IO.userError "dynamic optional type query mismatch")
  let some refFacts := node.compilerFacts | throw (IO.userError "dynamic-reference structural facts absent")
  let some compilerRefFacts := compilerNode.compilerFacts | throw (IO.userError "compiler dynamic-reference facts absent")
  check (refFacts.booleanQueries == compilerRefFacts.booleanQueries) "dynamic-reference boolean leaves differ"
  for unknown in #["is_freeze", "is_unpin", "is_unsafe_unpin"] do
    check ((facts.booleanQueries.find? (·.1 == unknown)).isNone) "solver fact fabricated"
  check ((facts.typeQueries.find? (·.1 == "pointer_metadata_type")).isNone) "nominal DynMetadata identity fabricated"
  let (again, againId) ← expect (r.intern ty)
  check (againId == id && again.types.size == r.types.size && again.predicates.size == r.predicates.size) "dyn pools not canonical"
  rejects ((PhysicalTypeRegistry.start {d with source := d.source.setObjVal! "dyn_metadata_source" Json.null}).intern ty)
  let evidence ← expect (d.source.getObjVal? "dyn_metadata_source")
  let wrapper ← expect (evidence.getObjVal? "non_null")
  let repr ← expect (wrapper.getObjVal? "repr")
  let changed := evidence.setObjVal! "non_null" (wrapper.setObjVal! "repr" (repr.setObjVal! "flags_bits" (toJson (8 : Nat))))
  rejects ((PhysicalTypeRegistry.start {d with source := d.source.setObjVal! "dyn_metadata_source" changed}).intern ty)
  let absent := Json.mkObj [("mode",toJson "metadata_lang_item_absent"),("metadata_type",Json.null)]
  rejects ((PhysicalTypeRegistry.start {d with source := d.source.setObjVal! "dyn_metadata_source" absent}).intern ty)
  let some entry := r.registry.entries[dynId]? | throw (IO.userError "dyn concrete type absent")
  rejects (layoutOfRuntime (← expect (runtimeTargetOfTarget d.target)) ty)
  rejects (layoutOfDocument d (.array entry.type 0))
  rejects (rustPassMode d.target "x86_64" true entry.type (some "No"))
  if node.shapeKind == .reference then
    let (_, abi) ← expect (rustFunctionAbiOfSourceSignature d definition #[])
    let some argument := abi.arguments[0]? | throw (IO.userError "dyn ABI argument absent")
    check (argument.mode.kind == .pair) "shared dyn argument ABI must be pair"
  else rejects (rustFunctionAbiOfSourceSignature d definition #[])
  IO.println "dynamic physical types: full compiler layouts, predicate joins and structural leaves match; unknown metadata/solver facts reject"
