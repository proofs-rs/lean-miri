import Miri.Input.Decoder
open Lean Miri.Input Miri.ABI
private def must [ToString ε] (value : Except ε α) : IO α :=
  match value with | .ok result => pure result | .error error => throw (IO.userError (toString error))
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
def main (args : List String) : IO Unit := do
  let [path,oraclePath] := args | throw (IO.userError "expected current source and independent Rust size oracle")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  IO.println s!"actual std decode PASS types={document.types.size} bodies={document.bodies.size}"
  let oracle ← must (Json.parse (← IO.FS.readFile oraclePath))
  let expected ← must ((← must (oracle.getObjVal? "parent_bytes")).getNat?)
  let target ← must (RuntimeMetadata.importTarget (← must (RuntimeMetadata.require document.runtimeTargetDataLayout "target")))
  let width (types : Array TypeNode) (definitions : Array DefinitionId) (id : Nat) :=
    RuntimeMetadata.scalarStorageSize target types document.layouts definitions document.typeConstants document.predicates id
  for id in #[2577,2578,10] do
    check ((← must (width document.types document.definitions id)) == expected) s!"raw storage width {id} differs from Rust"
  let parent ← must (RuntimeMetadata.require document.types[2577]? "parent")
  let field ← must (RuntimeMetadata.require document.types[2578]? "field")
  let .adt data := parent.shape | throw (IO.userError "expected actual transparent ADT")
  let .patternType base pattern := field.shape | throw (IO.userError "expected actual raw Pattern")
  check (base == 10) "actual Pattern base changed"
  check (!(RuntimeMetadata.resolveLayout target document.types document.layouts parent.layoutId document.definitions document.typeConstants document.predicates).isOk)
    "storage width silently changed full Pattern layout residual"
  let poisoned := document.types.map fun node =>
    if node.id == 2577 then { node with shape := .adt { data with variants := data.variants.map fun variant =>
      { variant with fields := variant.fields.map fun field => { field with typeId := 5 } } },compilerFacts := none }
    else { node with compilerFacts := none }
  check ((← must (width poisoned document.definitions 2577)) == expected) "width used cached fields or compilerFacts"
  let cycle := document.types.set! 2578 {field with shape := .patternType 2578 pattern}
  check (!(width cycle document.definitions 2578).isOk) "cyclic Pattern source succeeded"
  let dangling := document.types.set! 2578 {field with shape := .patternType document.types.size pattern}
  check (!(width dangling document.definitions 2578).isOk) "dangling Pattern source succeeded"
  let definition ← must (RuntimeMetadata.require document.definitions[data.definition]? "definition")
  let declaration ← must (RuntimeMetadata.require definition.adtDeclaration "raw declaration")
  let malformed := document.definitions.set! data.definition {definition with adtDeclaration := some {declaration with fields := #[]}}
  check (!(width document.types malformed 2577).isOk) "malformed raw declaration succeeded"
  let template ← must (RuntimeMetadata.require definition.genericTemplate "raw template")
  let sourceField ← must (RuntimeMetadata.require template.fields[0]? "raw field")
  let badPattern := GenericSubstitution.Term.node .type "pattern" ""
    (.cons (.atom .type "uint" "usize") (.cons (.atom .aggregate "pattern_range" "") .nil))
  let badTemplate := {template with fields := template.fields.set! 0 {sourceField with expression := badPattern}}
  let badDefs := document.definitions.set! data.definition {definition with genericTemplate := some badTemplate}
  check (!(width document.types badDefs 2577).isOk) "malformed raw Pattern expression succeeded"
  let nontransparentRepr := {declaration.representation with flagsBits := 0}
  let defs := document.definitions.set! data.definition {definition with adtDeclaration := some {declaration with representation := nontransparentRepr}}
  let types := document.types.set! 2577 {parent with shape := .adt {data with representation := nontransparentRepr}}
  check (!(width types defs 2577).isOk) "nontransparent aggregate bypassed full Pattern obligation"
  let context : DecodeMIR.Context := {
    typeCount := document.types.size,allocationCount := document.allocations.size,
    definitionCount := document.definitions.size,typeConstantCount := document.typeConstants.size,
    spanCount := document.spans.size,
    scalarSize := fun id => (width document.types document.definitions id).toOption }
  let _ ← must (DecodeMIR.resolveConstValue context 2577 (.Scalar (.Int 0 expected)))
  match DecodeMIR.resolveConstValue context 2577 (.Scalar (.Int 0 (expected + 1))) with
  | .error "scalar byte width disagrees with type 2577" => pure ()
  | _ => throw (IO.userError "wrong scalar wire width was accepted or changed failure")
  IO.println "storage controls PASS: raw ADT/Pattern/base Rust equality; poisoned fields/facts ignored; full-layout residual retained; cycle/dangling/malformed/nontransparent rejected"
