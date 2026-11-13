import Miri.Input.Decoder
import Miri.Input.AliasRuntime
import Miri.Input.SourceBuiltinDispatch
open Lean Miri.Input GenericSubstitution
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error e => throw (IO.userError e)
private def canonicalHeaders : Nat → GenericSubstitution.Term → Except String GenericSubstitution.Term
  | 0,_ => throw "signature payload canonicalization exhausted"
  | fuel+1,term => do
    match term with
    | .node .aggregate "signature" payload children =>
      let payload ← Json.parse payload
      return .node .aggregate "signature" payload.compress (← children.mapM (canonicalHeaders fuel))
    | .node sort tag payload children => return .node sort tag payload (← children.mapM (canonicalHeaders fuel))
    | .definition sort tag identity children => return .definition sort tag identity (← children.mapM (canonicalHeaders fuel))
    | .binder variables body => return .binder variables (← canonicalHeaders fuel body)
    | _ => pure term


def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected actual std source and Rust oracle")
  let document := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let context ← must (AliasRuntime.Context.ofDocument document)
  let oracle ← must (Json.parse (← IO.FS.readFile oraclePath))
  let some node := document.types[1257]? | throw (IO.userError "actual std FnDef1257 absent")
  let .functionDefinition physical arguments _ _ _ := node.shape | throw (IO.userError "actual FnDef absent")
  let some definition := document.definitions[physical]? | throw (IO.userError "method source absent")
  let some template := definition.genericTemplate | throw (IO.userError "method signature absent")
  let arena ← must (TypeArena.World.ofMaterial document.types document.typeConstants document.definitions
    document.predicates context.generic.pointerBytes)
  let arguments ← must (GenericInstantiationWorld.ofArguments arena 16384 arguments)
  let raw ← must (template.instantiateSignature 16384 arguments)
  let normalized ← must (AliasRuntime.normalizeTerm context 100000 16384 #[] #[] raw)
  let expected ← must (GenericMaterialCodec.readTerm 16384 (← must (oracle.getObjVal? "normalized_signature")))
  unless (← must (canonicalHeaders 16384 normalized)) == (← must (canonicalHeaders 16384 expected)) do
    throw (IO.userError "actual std1257 signature differs from independent Rust")
  IO.println "PASS actual std1257 original signature normalized against independent Rust"
  let rows ← must ((← must (oracle.getObjVal? "iterator_goals")).getArr?)
  for row in rows do
    let self ← must (GenericMaterialCodec.readTerm 16384 (← must (row.getObjVal? "self")))
    let name ← must ((← must (row.getObjVal? "name")).getStr?)
    let expected ← must ((← must ((← must (row.getObjVal? "result")).getObjVal? "kind")).getStr?)
    let actual ← must (AliasRuntime.solveGoal context 4096 100000
      ⟨.positive,⟨⟨2,11138⟩,#[self]⟩⟩)
    match actual with
    | .proven (.implementation selection _) =>
      unless expected == "implementation" do throw (IO.userError s!"false Iterator proof {name}")
      let expectedDefinition ← must (GenericMaterialCodec.readDefinition
        (← must ((← must (row.getObjVal? "result")).getObjVal? "definition")))
      unless selection.implementation == expectedDefinition do
        throw (IO.userError "actual Iterator selected a different physical impl")
    | .proven _ => throw (IO.userError "actual Iterator used a fabricated builtin proof")
    | .noSolution => unless expected == "no_solution" do throw (IO.userError s!"missing Iterator proof {name}")
    | .ambiguous why => throw (IO.userError s!"unexpected Iterator ambiguity {why}")
    IO.println s!"PASS actual Iterator {name}: {expected}"

  let some declaration := document.traitProgram.traits.find? (·.definition == (⟨2,11138⟩ : DefinitionIdentity))
    | throw (IO.userError "physical Iterator declaration absent")
  let controls : Array (String × GenericSubstitution.Term) := #[
    ("coroutine",.definition .type "coroutine" ⟨0,1⟩ .nil),
    ("dynamic",.node .type "dynamic" "" .nil),
    ("opaque",.definition .type "alias_opaque" ⟨0,1⟩ .nil),
    ("projection",.definition .type "alias_projection_not_rigid" ⟨0,1⟩ .nil),
    ("parameter",.parameter .type 0),
    ("unknown-head",.atom .type "unknown" "")]
  for (name,self) in controls do
    match SourceBuiltinDispatch.classify 4096 declaration #[self] with
    | .error _ => IO.println s!"PASS explicit conditional residual {name}"
    | .ok _ => throw (IO.userError s!"conditional builtin falsely classified residual {name}")
  let unknown := {declaration with langItem := some "future_unknown_language_trait"}
  match SourceBuiltinDispatch.classify 4096 unknown #[.atom .type "uint" "u8"] with
  | .error _ => IO.println "PASS unknown language trait explicit residual"
  | .ok _ => throw (IO.userError "unknown language trait silently absent")
