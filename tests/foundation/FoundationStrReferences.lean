import Miri.Frontend.FoundationSignatureFnAbi
import Miri.Frontend.FoundationPrimitiveFacts
import Miri.Input.Decoder

open Lean Miri Miri.Frontend.Foundation
private def expect (r : Except String α) : IO α :=
  match r with | .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def rejects (r : Except String α) : IO Unit :=
  match r with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported str ABI/facts accepted")

private def samePrimitive (left right : Input.TypeShape) : Bool :=
  match left, right with
  | .str, .str => true
  | .tuple l, .tuple r => l.isEmpty && r.isEmpty
  | .uint (.known l), .uint (.known r) => l == r
  | _ , _ => false

def main (paths : List String) : IO Unit := do
  let [sourcePath, referencePath] := paths
    | throw (IO.userError "usage: FoundationStrReferences FOUNDATION_JSON SCHEMA12_REFERENCE")
  let d ← expect (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let some body := d.bodies[0]? | throw (IO.userError "literal source missing")
  let definition ← expect (body.getObjValAs? Nat "definition")
  let (r, abi) ← expect (rustFunctionAbiOfSourceSignature d definition #[])
  let r ← expect r.withPrimitiveFacts
  check (abi.returnValue.mode.kind == .pair && abi.returnValue.mode.attributes.size == 2) "str scalar pair ABI"
  let reference ← expect (Input.decodeJson (← IO.FS.readFile referencePath))
  let reference := reference.document
  let runtime ← expect ((Input.RuntimeMetadata.ofDocument reference).mapError toString)
  let some root := reference.bodyRoots[0]? | throw (IO.userError "reference root absent")
  let some query := reference.queries.instanceAbis.find? (fun q => q.instanceId == root.entryInstance && q.extraArgumentTypes.isEmpty)
    | throw (IO.userError "reference root ABI absent")
  let some compilerAbi := reference.functionAbis[query.abiId]? | throw (IO.userError "reference ABI row absent")
  let (node, _) ← expect (r.lookup abi.returnValue.typeId)
  let .reference strId .Not .Erased := node.shape | throw (IO.userError "source str return shape")
  let compilerNode ← expect ((runtime.node compilerAbi.returnValue.typeId).mapError toString)
  let .reference compilerStrId .Not .Erased := compilerNode.shape | throw (IO.userError "reference str return shape")
  -- Source table IDs are compilation-local. Rebind only after exact shape joins;
  -- all other ABI fields, including every attribute field, compare unchanged.
  let rebased := {abi with returnValue := {abi.returnValue with
    typeId := compilerAbi.returnValue.typeId, layoutId := compilerAbi.returnValue.layoutId}}
  check (rebased == compilerAbi) "complete FnAbi differs from compiler reference"
  let physical ← expect (r.runtimeLayout abi.returnValue.typeId)
  let compilerPhysical ← expect ((runtime.lookup compilerAbi.returnValue.typeId).mapError toString)
  check (physical.layout == compilerPhysical.layout) "wide reference physical layout differs"
  let strPhysical ← expect (r.runtimeLayout strId)
  let compilerStrPhysical ← expect ((runtime.lookup compilerStrId).mapError toString)
  check (strPhysical.layout == compilerStrPhysical.layout) "str physical layout differs"
  let (strNode, _) ← expect (r.lookup strId)
  let compilerStr ← expect ((runtime.node compilerStrId).mapError toString)
  let some facts := strNode.compilerFacts | throw (IO.userError "str facts absent")
  let some compilerFacts := compilerStr.compilerFacts | throw (IO.userError "compiler str facts absent")
  check (facts.typingEnvironment == compilerFacts.typingEnvironment && facts.booleanQueries == compilerFacts.booleanQueries)
    "str boolean compiler leaves differ"
  let some discriminants := facts.discriminants | throw (IO.userError "str discriminants absent")
  let some compilerDiscriminants := compilerFacts.discriminants | throw (IO.userError "compiler str discriminants absent")
  check (discriminants.hasDiscriminants == compilerDiscriminants.hasDiscriminants &&
    discriminants.adtVariantCount == compilerDiscriminants.adtVariantCount &&
    discriminants.values.isEmpty && compilerDiscriminants.values.isEmpty) "str discriminant fields differ"
  check (facts.typeQueries.size == compilerFacts.typeQueries.size) "str type-query domain differs"
  for (name, value) in facts.typeQueries do
    let some (_, compilerValue) := compilerFacts.typeQueries.find? (·.1 == name)
      | throw (IO.userError "compiler type query absent")
    match value, compilerValue with
    | none, none => pure ()
    | some id, some compilerId =>
      let (localNode, _) ← expect (r.lookup id)
      let referenceNode ← expect ((runtime.node compilerId).mapError toString)
      check (samePrimitive localNode.shape referenceNode.shape) s!"str type query {name} differs"
    | _, _ => throw (IO.userError "str type query optional answer differs")
  let some referenceFacts := node.compilerFacts | throw (IO.userError "reference leaves absent")
  let some compilerReferenceFacts := compilerNode.compilerFacts | throw (IO.userError "compiler reference leaves absent")
  check (referenceFacts.typingEnvironment == compilerReferenceFacts.typingEnvironment &&
    referenceFacts.booleanQueries == compilerReferenceFacts.booleanQueries &&
    referenceFacts.typeQueries.size == compilerReferenceFacts.typeQueries.size) "reference leaf domains differ"
  for (name, value) in referenceFacts.typeQueries do
    let some (_, compilerValue) := compilerReferenceFacts.typeQueries.find? (·.1 == name)
      | throw (IO.userError "compiler reference type query absent")
    if name == "normalized" || name == "metadata_tail" then
      check (value == some node.id && compilerValue == some compilerNode.id) "reference self query differs"
    else
      match value, compilerValue with
      | none, none => pure ()
      | some id, some compilerId =>
        let (localNode, _) ← expect (r.lookup id)
        let referenceNode ← expect ((runtime.node compilerId).mapError toString)
        check (samePrimitive localNode.shape referenceNode.shape) s!"reference type query {name} differs"
      | _, _ => throw (IO.userError "reference optional query answer differs")
  let ty := ConcreteType.pointer "reference_erased_const" (.primitive "str" "")
  rejects (rustPassMode d.target "x86_64" true ty)
  rejects (rustPassMode d.target "x86_64" true ty (some "Aggressive"))
  let argument ← expect (rustPassMode d.target "x86_64" false ty (some "No"))
  check (argument.kind == .pair && argument.attributes == abi.returnValue.mode.attributes) "optNo str argument attributes"
  rejects (rustPassMode d.target "x86_64" false ty (some "Aggressive"))
  rejects (rustPassMode d.target "x86_64" true (.pointer "reference_erased_mut" (.primitive "str" "")) (some "No"))
  rejects (rustPassMode d.target "x86_64" true (.pointer "raw_pointer_const" (.primitive "str" "")) (some "No"))
  rejects (primitiveCompilerFacts (.primitive "str" "") 0 1 2)
  rejects (primitiveFactsDomain (.array (.primitive "str" "") 1))
  rejects (rustPassMode d.target "x86_64" true (.primitive "str" "") (some "No"))
  IO.println "str references: full compiler ABI/layout and implemented bool/type-query leaves match; unsupported modes reject"
