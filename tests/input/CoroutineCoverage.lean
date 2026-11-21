import MiriTests.Input.JsonFixtures
import Miri.Input.Decoder

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def object (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map fun (key,value) => Json.renderString key ++ ":" ++ value) ++ "}"
private def setField (source key value : String) : Except String String := do
  let fields ← (← JsonFixtures.parse source).object
  let retained := fields.filterMap fun (name, child) => if name == key then none else some (name,child.text)
  pure (object ((key,value)::retained.toList))
private def rejected (source : String) (fragment : String) : IO Unit :=
  match decodeJson source with
  | .ok _ => throw (IO.userError s!"malformed coroutine evidence accepted: {fragment}")
  | .error error => check ((error.splitOn fragment).length > 1) s!"wrong rejection: {error}; expected {fragment}"

private def invalidCoverage (document : ImportDocument) (value : CoroutineCoverage) (fragment : String) : IO Unit :=
  match CoroutineCoverageCodec.validate document value with
  | .ok _ => throw (IO.userError s!"constructed malformed coverage accepted: {fragment}")
  | .error error => check ((error.splitOn fragment).length > 1) s!"wrong component rejection: {error}; expected {fragment}"

/-- Constructed metadata controls exercise validators; they are neither compiler
exports nor evidence of safe coroutine execution. -/
private def componentChecks (original : ImportDocument) : IO Unit := do
  let some owner := original.bodies[0]? | throw (IO.userError "missing fixture body")
  let some sourceInstance := original.instances[owner.instanceId]? | throw (IO.userError "missing fixture instance")
  let some definition := owner.definitionId | throw (IO.userError "missing fixture definition")
  let ownerInstance := {sourceInstance with instanceKind := .Item definition}
  let some sourceType := original.types[0]? | throw (IO.userError "missing fixture type")
  let material : SourceCoroutineLayout := ⟨#[], #[], #[], #[#[], #[], #[]], #[], 0, .Movable, #[]⟩
  let ty := {sourceType with
    shape := .coroutine definition ownerInstance.genericArgs
    sourceLayout := {normalizedType := 0, coroutine := some material}}
  let document := {original with
    types := original.types.set! 0 ty
    instances := original.instances.set! owner.instanceId ownerInstance}
  let source : Miri.Input.SourceInfo := ⟨owner.spanId, 0⟩
  let row : CoroutineEvidence := ⟨0, 0, .Coroutine .Movable, none, none,
    ⟨#[], #[#[], #[], #[]], #[source, source, source], #[]⟩, some 0, none, some 1, none⟩
  let sync : CoroutineAuxiliaryBody := ⟨0, .sync, .Shim (.DropGlue definition (some 0)),
    {owner with mir := {owner.mir with phase := .Runtime .Initial}}⟩
  let proxy : CoroutineAuxiliaryBody := ⟨0, .proxyAsync, ownerInstance.instanceKind,
    {owner with mir := {owner.mir with phase := .Analysis .PostCleanup}}⟩
  let coverage : CoroutineCoverage := ⟨#[true], #[row], #[sync, proxy]⟩
  let _ ← must (CoroutineCoverageCodec.validate document coverage)
  let wrongType := {ty with sourceLayout := {ty.sourceLayout with coroutine := some {material with movability := .Static}}}
  let wrongMovability := {document with types := document.types.set! 0 wrongType}
  invalidCoverage wrongMovability coverage "source movability differs from body kind"
  let asyncRow := {row with dropSync := none, dropProxyAsync := none, dropAsync := some 0}
  let asyncBody := {proxy with role := .async}
  let _ ← must (CoroutineCoverageCodec.validate document {coverage with coroutines := #[asyncRow], auxiliaryBodies := #[asyncBody]})
  invalidCoverage document {coverage with coroutines := #[row, row]} "duplicate owner"
  invalidCoverage document {coverage with bodyCoroutines := #[false]} "missing marker"
  invalidCoverage document {coverage with coroutines := #[{row with coroutineType := original.types.size}]} "missing coroutine type"
  invalidCoverage document {coverage with coroutines := #[{row with yieldType := some 0}]} "unlowered yield/resume"
  invalidCoverage document {coverage with coroutines := #[{row with resumeType := some 0}]} "unlowered yield/resume"
  invalidCoverage document {coverage with coroutines := #[{row with layout := {row.layout with variantSources := #[]}}]} "layout dimensions"
  let saved : CoroutineSavedField := ⟨0, source, false, none⟩
  let oneField := {row.layout with fields := #[saved], storageConflicts := #[#[]]}
  invalidCoverage document {coverage with coroutines := #[{row with layout := {oneField with fields := #[{saved with typeId := original.types.size}]}}]} "dangling saved field type"
  invalidCoverage document {coverage with coroutines := #[{row with layout := {oneField with fields := #[{saved with sourceInfo := ⟨original.spans.size, 0⟩}]}}]} "dangling source info"
  invalidCoverage document {coverage with coroutines := #[{row with layout := {oneField with fields := #[{saved with sourceInfo := ⟨source.spanId, owner.sourceScopes.size⟩}]}}]} "dangling source info"
  invalidCoverage document {coverage with coroutines := #[{row with layout := {oneField with variants := #[#[1], #[], #[]]}}]} "invalid or duplicate saved field index"
  invalidCoverage document {coverage with coroutines := #[{row with layout := {oneField with variants := #[#[0, 0], #[], #[]]}}]} "invalid or duplicate saved field index"
  invalidCoverage document {coverage with coroutines := #[{row with layout := {oneField with storageConflicts := #[#[1]]}}]} "invalid or duplicate saved field index"
  invalidCoverage document {coverage with coroutines := #[{row with layout := {row.layout with fields := #[saved, saved], storageConflicts := #[#[1], #[]]}}]} "asymmetric storage conflicts"
  invalidCoverage document {coverage with coroutines := #[{row with dropSync := none, dropProxyAsync := none}]} "inconsistent drop roles"
  invalidCoverage document {coverage with coroutines := #[{row with dropSync := some 2}]} "dangling auxiliary body"
  invalidCoverage document {coverage with auxiliaryBodies := #[{sync with role := .async}, proxy]} "mismatched auxiliary role/owner"
  invalidCoverage document {coverage with auxiliaryBodies := #[{sync with ownerBody := 1}, proxy]} "mismatched auxiliary role/owner"
  invalidCoverage document {coverage with auxiliaryBodies := #[{sync with sourceKind := .Item definition}, proxy]} "no exact DropGlue source"
  invalidCoverage document {coverage with auxiliaryBodies := #[{sync with sourceKind := .Shim (.DropGlue definition (some 1))}, proxy]} "sync drop type differs"
  invalidCoverage document {coverage with auxiliaryBodies := #[sync, {proxy with sourceKind := .Item (definition + 1)}]} "auxiliary source kind differs from body definition"
  invalidCoverage document {coverage with auxiliaryBodies := #[sync, {proxy with body := {proxy.body with mir := {proxy.body.mir with phase := .Runtime .Optimized}}}]} "unexpected auxiliary snapshot phase"
  invalidCoverage document {coverage with auxiliaryBodies := #[sync, proxy, proxy]} "orphan auxiliary body"
  let some block := owner.mir.basicBlocks[0]? | throw (IO.userError "missing fixture block")
  let residualBlock := {block with terminator := {block.terminator with kind := .CoroutineDrop}}
  let residual := {owner with mir := {owner.mir with basicBlocks := owner.mir.basicBlocks.set! 0 residualBlock}}
  invalidCoverage {document with bodies := document.bodies.set! 0 residual} coverage "unlowered terminator"
  invalidCoverage document {coverage with auxiliaryBodies := #[{sync with body := {residual with mir := {residual.mir with phase := .Runtime .Initial}}}, proxy]} "unlowered terminator"
  invalidCoverage document {coverage with auxiliaryBodies := #[{sync with body := {sync.body with definitionId := none}}, proxy]} "auxiliary source kind differs from body definition"
  -- Physical layouts now come from source material; there is no selected-layout
  -- or field-query row to forge. Check the computed tag and state through the
  -- same provider used during execution, then reject disagreeing source material.
  let multiMaterial : SourceCoroutineLayout := ⟨#[1], #[1], #[], #[#[], #[], #[], #[0]], #[#[]], 43, .Movable, #[⟨1,false⟩]⟩
  let multiType := {ty with sourceLayout := {ty.sourceLayout with coroutine := some multiMaterial}}
  let multiDocument := {document with types := document.types.set! 0 multiType}
  let multiRow := {row with layout := ⟨#[⟨1, source, false, none⟩],
    #[#[], #[], #[], #[0]], #[source, source, source, source], #[#[]]⟩}
  let multiCoverage := {coverage with coroutines := #[multiRow]}
  let _ ← must (CoroutineCoverageCodec.validate multiDocument multiCoverage)
  let runtime ← must (RuntimeMetadata.ofDocument multiDocument |>.mapError toString)
  let root ← must (runtime.lookup 0 |>.mapError toString)
  check (root.layout.size.bytes == 2 && root.layout.randomizationSeed == 43) "computed coroutine root geometry/seed differs"
  let .Multiple tag .Direct tagIndex states := root.layout.variants |
    throw (IO.userError "computed coroutine did not retain direct state variants")
  check (tagIndex == 0 && states.size == 4) "computed coroutine tag/state count differs"
  check ((← must (tag.validRange runtime.target |>.mapError reprStr)) == ⟨0,3⟩) "computed coroutine tag range differs"
  let tagField ← must (runtime.field root 0 |>.mapError toString)
  let plainU8 ← must (runtime.lookup 1 |>.mapError toString)
  check (tagField.ty == plainU8.ty && tagField.layout != plainU8.layout) "computed tag lost its narrowed scalar range"
  for state in [:4] do
    let selected ← must (runtime.forVariant root state |>.mapError toString)
    check (selected.layout.size.bytes == 2) "computed state size differs from prefix storage"
    check (selected.layout.fields.count == (if state == 3 then 1 else 0)) "computed state field count differs"
    if state == 3 then
      let offset ← must (selected.layout.fields.offset 0 |>.mapError reprStr)
      check (offset.bytes == 1) "computed saved-field offset differs"
      let savedField ← must (runtime.field selected 0 |>.mapError toString)
      check (savedField == plainU8) "computed saved field differs from exact type layout"
  let noMaterial := {multiType with sourceLayout := {multiType.sourceLayout with coroutine := none}}
  invalidCoverage {multiDocument with types := multiDocument.types.set! 0 noMaterial}
    multiCoverage "missing source layout material"
  for badMaterial in #[
      {multiMaterial with savedTypes := #[2]},
      {multiMaterial with variants := #[#[], #[], #[], #[]]},
      {multiMaterial with conflicts := #[#[0]]}] do
    let wrongType := {multiType with sourceLayout := {multiType.sourceLayout with coroutine := some badMaterial}}
    invalidCoverage {multiDocument with types := multiDocument.types.set! 0 wrongType}
      multiCoverage "source layout differs from saved-local evidence"
  IO.println "PASS constructed coroutine ownership/type/index/conflict/phase/role/residual negatives"

/-- Finite schema-17 decoder controls and constructed source-layout witnesses;
these checks do not execute a Rust coroutine or establish guest safety. -/
def main : IO Unit := do
  let input ← IO.FS.readFile "tests/input/fixtures/strict-unit.json"
  let decoded ← must (decodeJson input)
  check decoded.document.coroutineCoverage.isSome "schema 17 lost typed coroutine coverage"
  let count := decoded.document.bodies.size
  let markers := "[" ++ String.intercalate "," (List.replicate count "false") ++ "]"
  let catalog := object [("body_coroutines", markers), ("coroutines", "[]"), ("auxiliary_bodies", "[]")]
  let valid ← must (setField input "compiler_coroutine_coverage" catalog)
  let newDecoded ← must (decodeJson valid)
  check newDecoded.document.coroutineCoverage.isSome "schema 17 failed to retain typed coverage"
  for version in ["11", "12", "13", "14", "15", "16", "18"] do
    rejected (← must (setField valid "schema_version" version)) "unsupported schema version"
  let fields ← must ((← must (JsonFixtures.parse valid)).object)
  let missingCoverage := object ((fields.filterMap fun (name, value) =>
    if name == "compiler_coroutine_coverage" then none else some (name,value.text)).toList)
  rejected missingCoverage "source coverage is absent"
  rejected (← must (setField valid "compiler_coroutine_coverage" (object [("auxiliary_bodies", "[]"), ("coroutines", "[]")]))) "body_coroutines"
  let badMarkers ← must (setField catalog "body_coroutines" "[]")
  rejected (← must (setField valid "compiler_coroutine_coverage" badMarkers)) "incomplete body markers"
  let marked := "[" ++ String.intercalate "," ("true" :: List.replicate (count - 1) "false") ++ "]"
  let missingWitness ← must (setField catalog "body_coroutines" marked)
  rejected (← must (setField valid "compiler_coroutine_coverage" missingWitness)) "marked body has no witness"
  let unknown ← must (setField catalog "unknown_witness" "true")
  rejected (← must (setField valid "compiler_coroutine_coverage" unknown)) "unknown coroutine catalog field"
  let badRole ← must (setField catalog "auxiliary_bodies" "[{\"role\":\"callable\"}]")
  rejected (← must (setField valid "compiler_coroutine_coverage" badRole)) "unknown coroutine auxiliary role"
  let badKind ← must (setField catalog "coroutines" "[{\"coroutine_kind\":{\"kind\":\"future_guess\"}}]")
  rejected (← must (setField valid "compiler_coroutine_coverage" badKind)) "unknown coroutine kind"
  let badKindFields ← must (setField catalog "coroutines" "[{\"coroutine_kind\":{\"kind\":\"coroutine\",\"movability\":\"movable\",\"source\":\"function\"}}]")
  rejected (← must (setField valid "compiler_coroutine_coverage" badKindFields)) "incompatible coroutine kind fields"
  let unknownKindField ← must (setField catalog "coroutines" "[{\"coroutine_kind\":{\"unverified\":true}}]")
  rejected (← must (setField valid "compiler_coroutine_coverage" unknownKindField)) "unknown coroutine kind field"
  let unknownSourceKind ← must (setField catalog "auxiliary_bodies" "[{\"source_kind\":{\"unverified\":true}}]")
  rejected (← must (setField valid "compiler_coroutine_coverage" unknownSourceKind)) "unknown coroutine source-kind field"
  let unknownRow ← must (setField catalog "coroutines" "[{\"unknown_witness\":0}]")
  rejected (← must (setField valid "compiler_coroutine_coverage" unknownRow)) "unknown coroutine coverage field"
  -- Parser-only control: pooling preserves exact saved-local source metadata.
  -- Semantic acceptance is tested separately above and by componentChecks.
  let pools ← must (JsonReader.run (do
    let pools ← readSharedPools
    JsonReader.skipValue
    pure pools) input)
  let layout := object [("field_tys", "[{\"type\":0,\"source_info\":0,\"ignore_for_traits\":false,\"debuginfo_name\":null}]"),
    ("variant_fields", "[[],[],[]]"), ("variant_source_info", "[]"), ("storage_conflicts", "[[]]")]
  let witness := object [("owner_body", "0"), ("coroutine_type", "0"),
    ("coroutine_kind", "{\"kind\":\"coroutine\",\"movability\":\"movable\"}"),
    ("yield_type", "null"), ("resume_type", "null"), ("layout", layout),
    ("drop_sync", "null"), ("drop_async", "null"), ("drop_proxy_async", "null")]
  let parserCatalog := object [("body_coroutines", "[true]"), ("coroutines", "[" ++ witness ++ "]"), ("auxiliary_bodies", "[]")]
  let parsed ← must (JsonReader.run (CoroutineCoverageCodec.parse pools.mir) parserCatalog)
  let some savedSource := (parsed.value.coroutines[0]?).bind fun row => row.layout.fields[0]?.map (·.sourceInfo) |
    throw (IO.userError "pooled saved source disappeared")
  check (some savedSource == pools.mir.sources[0]?) "saved source pool reference changed"
  let badSavedSource ← must (setField layout "field_tys" "[{\"type\":0,\"source_info\":999999,\"ignore_for_traits\":false,\"debuginfo_name\":null}]")
  let badWitness ← must (setField witness "layout" badSavedSource)
  let badCatalog ← must (setField catalog "coroutines" ("[" ++ badWitness ++ "]"))
  rejected (← must (setField valid "compiler_coroutine_coverage" badCatalog)) "dangling source-info pool reference"
  componentChecks decoded.document
  IO.println "PASS strict schema-17 coroutine coverage, computed layouts and malformed/missing/unknown guards"
