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

private def showNode (value : Except RuntimeMetadataError TypeNode) : String :=
  match value with
  | .error e => render e
  | .ok node => s!"{node.id}:{node.payload.compress}"

#eval do
  let raw ← IO.FS.readFile "scratch/regression-inputs/u32.schema3.json"
  let decoded ← match Miri.Input.decodeJson raw with
    | .ok value => pure value
    | .error e => throw <| IO.userError s!"root_u32 decode failed: {e}"
  let document := decoded.document
  let metadata ← match RuntimeMetadata.ofDocument document with
    | .ok value => pure value
    | .error e => throw <| IO.userError s!"root_u32 metadata failed: {e}"
  let uncached := { metadata with nodeCache := none, layoutCache := none }
  let mut lookupsAgree := true
  for node in document.types do
    lookupsAgree := lookupsAgree &&
      showNode (metadata.node node.id) == showNode (uncached.node node.id) &&
      showResult (metadata.lookup node.id) == showResult (uncached.lookup node.id)
  let indexed := RuntimeMetadata.Indexed.ofMetadata metadata
  for node in document.types do
    lookupsAgree := lookupsAgree &&
      showNode (indexed.node node.id) == showNode (uncached.node node.id) &&
      showResult (indexed.lookup node.id) == showResult (uncached.lookup node.id)
  assertTrue "root_u32 cached/uncached/indexed node and layout lookups" lookupsAgree
  let primitiveCache := CompilerPrimitiveFacts.bind metadata
  let mut primitiveAgree := true
  for key in #["bool", "i8", "i16", "i32", "i64", "i128", "u8", "u16", "u32", "u64", "u128", "usize", "isize", "unit", "unit_pointer_const", "unit_pointer_mut"] do
    primitiveAgree := primitiveAgree &&
      showResult (CompilerPrimitiveFacts.primitiveLayout metadata key) ==
      showResult (CompilerPrimitiveFacts.primitiveLayoutBound metadata primitiveCache key)
  primitiveAgree := primitiveAgree &&
    showResult (CompilerPrimitiveFacts.orderingLayout metadata) ==
      showResult (CompilerPrimitiveFacts.orderingLayoutBound metadata primitiveCache) &&
    showResult (CompilerPrimitiveFacts.callerLocationType metadata) ==
      showResult (CompilerPrimitiveFacts.callerLocationTypeBound metadata primitiveCache)
  assertTrue "root_u32 exact primitive, ordering, and caller-location cache outputs" primitiveAgree
  let sourceFirstUnit := document.types.find? (fun (node : TypeNode) =>
    node.shapeKind == TypeShapeKind.tuple &&
      ((node.payload.getObjVal? "shape").bind fun shape =>
        (shape.getObjVal? "elements").bind Json.getArr?).toOption == some #[])
  let unitResult := CompilerPrimitiveFacts.unitLayout metadata
  let cachedUnit := CompilerPrimitiveFacts.unitLayoutBound metadata primitiveCache
  assertTrue "unit query preserves its source primitive result" (showResult unitResult == showResult cachedUnit)
  let indexedRuntime := RuntimeMetadata.Indexed.ofMetadata metadata
  let unitCache := Miri.Input.CompilerFacts.bindUnitLayout indexedRuntime
  let strictTuple := RuntimeMetadata.findKind metadata TypeShapeKind.tuple
  let expectedUnit := match sourceFirstUnit with
    | some node => showResult (metadata.lookup node.id)
    | none => "none"
  assertTrue "first empty-tuple unit lookup" (showResult unitCache.value == expectedUnit)
  let missingKey := "qa_missing_primitive"
  let missingBase := CompilerPrimitiveFacts.primitiveLayout metadata missingKey
  let missingCached := CompilerPrimitiveFacts.primitiveLayoutBound metadata primitiveCache missingKey
  assertTrue "missing primitive fallback preserves error" (showResult missingBase == showResult missingCached)
  let firstType : TypeNode ← match document.types[0]? with
    | some node => pure node
    | none => throw <| IO.userError "root_u32 fixture unexpectedly has no types"
  let duplicateDocument := { document with types := document.types.push firstType }
  let duplicateResult := RuntimeMetadata.ofDocument duplicateDocument
  let duplicatePrecedence := match duplicateResult with
    | .error (.duplicateType duplicateId) => duplicateId == firstType.id
    | _ => false
  assertTrue "duplicate type error remains before per-row layout conversion" duplicatePrecedence
  IO.println s!"typedTreeRoot={match document.typedTree with | .object fields => s!"object:{fields.size}" | .array values => s!"array:{values.size}" | .statement .. => "statement" | .terminator .. => "terminator" | .rvalue .. => "rvalue" | .operand .. => "operand" | .projection .. => "projection" | _ => "other"}"
  IO.println s!"obligations={render decoded.blockingObligations}"
  IO.println s!"readiness={decoded.executionInput.isSome}"
  IO.println s!"primitiveCache=PASS unitFirstMatch={render (sourceFirstUnit.map (fun (node : TypeNode) => node.id))} unit={showResult unitResult} strictTuple={showResult strictTuple} missing={showResult missingBase} duplicateError={duplicatePrecedence}"
