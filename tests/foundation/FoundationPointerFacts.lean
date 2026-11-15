import Miri.Frontend.FoundationPrimitiveFacts
import Miri.Frontend.FoundationSignatureFnAbi
import Miri.Input.Decoder

open Lean Miri Miri.Frontend.Foundation

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

/-- Compare each derived pointer boolean/type leaf with a genuine fresh
ordinary export. Translate only validated shared primitive/root identities. -/
def main (paths : List String) : IO Unit := do
  let [foundationPath, compilerPath] := paths
    | throw (IO.userError "expected foundation and ordinary pointer identity exports")
  let document ← checked (Json.parse (← IO.FS.readFile foundationPath) >>= decode)
  let some body := document.bodies[0]? | throw (IO.userError "source body absent")
  let definition ← checked (body.getObjValAs? Nat "definition")
  let (initial, abi) ← checked (rustFunctionAbiOfSourceSignature document definition #[])
  let physical ← checked initial.withPrimitiveFacts
  let (node, _) ← checked (physical.lookup abi.returnValue.typeId)
  let some computed := node.compilerFacts | throw (IO.userError "computed pointer facts absent")
  let compiler ← checked (Input.decodeJson (← IO.FS.readFile compilerPath))
  let doc := compiler.document
  let some root := doc.bodyRoots[0]? | throw (IO.userError "compiler root absent")
  let some sourceBody := doc.bodies[root.bodyId]? | throw (IO.userError "compiler body absent")
  let some actualId := sourceBody.mir.locals[0]? | throw (IO.userError "compiler return type absent")
  let some actualNode := doc.types[actualId]? | throw (IO.userError "compiler pointer node absent")
  let some actual := actualNode.compilerFacts | throw (IO.userError "compiler pointer facts absent")
  let (physical, unitId) ← checked (physical.intern (.tuple #[]))
  let (_, u8Id) ← checked (physical.intern (.primitive "uint" "u8"))
  let mapping := #[(node.id, actualId), (unitId, doc.queries.primitives.unit), (u8Id, doc.queries.primitives.u8)]
  unless computed.booleanQueries == actual.booleanQueries do
    throw (IO.userError "pointer boolean compiler leaves differ")
  for (name, value) in computed.typeQueries do
    let translated ← value.mapM fun id => do
      let some (_, mapped) := mapping.find? (·.1 == id)
        | throw (IO.userError s!"pointer fact {name} references unmapped physical type")
      return mapped
    unless actual.typeQueries.find? (·.1 == name) == some (name, translated) do
      throw (IO.userError s!"pointer type compiler leaf {name} differs")
  let some discriminants := computed.discriminants | throw (IO.userError "computed discriminants absent")
  let some actualDiscriminants := actual.discriminants | throw (IO.userError "compiler discriminants absent")
  unless discriminants.hasDiscriminants == actualDiscriminants.hasDiscriminants &&
      discriminants.adtVariantCount == actualDiscriminants.adtVariantCount &&
      discriminants.values.isEmpty && actualDiscriminants.values.isEmpty do
    throw (IO.userError "pointer discriminant compiler leaves differ")
  unless computed.typeIdHash.isNone do throw (IO.userError "unimplemented hash fabricated")
  for unsupported in #[ConcreteType.pointer "reference_erased_const" (.primitive "uint" "u8"),
      .pointer "raw_pointer_const" (.primitive "str" "")] do
    match primitiveFactsDomain unsupported with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "unsupported reference/str pointer compiler facts accepted")
  IO.println "foundation pointer facts: all emitted boolean/type/discriminant leaves match fresh compiler metadata; references/str reject"
