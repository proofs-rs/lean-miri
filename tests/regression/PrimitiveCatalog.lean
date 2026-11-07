import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.CompilerFacts

open Lean
open Miri.Input
open Miri.Input.RuntimeMetadata

private def assertTrue (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw <| IO.userError s!"FAIL: {label}"

private def render (value : α) [Repr α] : String := reprStr value

private def showResult {ε : Type} (value : Except ε α) [Repr ε] [Repr α] : String := render value

#eval do
  let raw ← IO.FS.readFile "examples/empty_function/input.json"
  let decoded ← match Miri.Input.decodeJson raw with
    | .ok value => pure value
    | .error e => throw <| IO.userError s!"fixed source decode failed: {e}"
  let document := decoded.document
  let metadata ← match RuntimeMetadata.ofDocument document with
    | .ok value => pure value
    | .error e => throw <| IO.userError s!"fixed source metadata failed: {e}"
  for node in document.types do
    assertTrue "type ID addresses its source row"
      ((metadata.node node.id).toOption.map (fun (value : TypeNode) => value.id) == some node.id)
  for key in #["u8", "u16", "u32", "usize", "unit"] do
    let layout ← match CompilerPrimitiveFacts.primitiveLayout metadata key with
      | .ok value => pure value
      | .error reason => throw <| IO.userError reason
    assertTrue "primitive type identity matches reader catalog"
      ((CompilerPrimitiveFacts.primitiveType metadata key).toOption == some layout.ty)
  let sourceFirstUnit := document.types.find? (fun (node : TypeNode) =>
    node.shapeKind == TypeShapeKind.tuple &&
      ((node.relations.elements.bind fun id =>
        (document.typeRelationTables.typeLists.lookup id).toOption) == some #[]))
  let unitResult := CompilerPrimitiveFacts.unitLayout metadata
  let indexedRuntime := RuntimeMetadata.Indexed.ofMetadata metadata
  let unitCache := Miri.Input.CompilerFacts.bindUnitLayout indexedRuntime
  let strictTuple := RuntimeMetadata.findKind metadata TypeShapeKind.tuple
  let expectedUnit := match sourceFirstUnit with
    | some node => showResult (metadata.lookup node.id)
    | none => "none"
  assertTrue "first empty-tuple unit lookup" (showResult unitCache.value == expectedUnit)
  let missingKey := "qa_missing_primitive"
  let missingBase := CompilerPrimitiveFacts.primitiveLayout metadata missingKey
  assertTrue "missing primitive remains a failure" missingBase.toOption.isNone
  let firstType : TypeNode ← match document.types[0]? with
    | some node => pure node
    | none => throw <| IO.userError "fixed source fixture unexpectedly has no types"
  let duplicateDocument := { document with types := document.types.push firstType }
  let duplicateResult := RuntimeMetadata.ofDocument duplicateDocument
  let duplicatePrecedence := match duplicateResult with
    | .error (.duplicateType duplicateId) => duplicateId == firstType.id
    | _ => false
  assertTrue "duplicate type error remains before per-row layout conversion" duplicatePrecedence
  IO.println s!"typedTreeRoot={match document.typedTree with | .object fields => s!"object:{fields.size}" | .array values => s!"array:{values.size}" | .statement .. => "statement" | .terminator .. => "terminator" | .rvalue .. => "rvalue" | .operand .. => "operand" | .projection .. => "projection" | _ => "other"}"
  IO.println s!"obligations={render decoded.blockingObligations}"
  IO.println s!"readiness={decoded.executionInput.isSome}"
  IO.println s!"primitiveCatalog=PASS unitFirstMatch={render (sourceFirstUnit.map (fun (node : TypeNode) => node.id))} unit={showResult unitResult} strictTuple={showResult strictTuple} missing={showResult missingBase} duplicateError={duplicatePrecedence}"
