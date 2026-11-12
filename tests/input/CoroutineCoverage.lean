import MiriTests.Input.JsonFixtures
import MiriTests.Input.LegacyFixture
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
private def withoutField (source key : String) : Except String String := do
  let fields ← (← JsonFixtures.parse source).object
  pure (object (fields.toList.filterMap fun (name, child) =>
    if name == key then none else some (name, child.text)))
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
  let initial ← must (TypeArena.World.ofDocument original)
  let (ownerCore,arena) ← must ((SourceMir.resolveBody original 0).run initial)
  unless arena.constructedTypes.isEmpty && arena.constructedConstants.isEmpty do
    throw (IO.userError "component material mutation cannot discard constructed identities")
  let some ownerSeed := original.bodies[0]? | throw (IO.userError "missing fixture body seed")
  let owner : Body := {toBodyCore := ownerCore, promotedBodies := ownerSeed.promotedBodies}
  let some ownerInstance := original.instances[owner.instanceId]? | throw (IO.userError "missing fixture instance")
  let .Item definition := ownerInstance.instanceKind | throw (IO.userError "fixture owner is not Item")
  let some sourceType := original.types[0]? | throw (IO.userError "missing fixture type")
  let facts : TypeCompilerFacts := {
    typingEnvironment := "fully_monomorphized", booleanQueries := #[], typeQueries := #[]
    projectionQueries := some ⟨"fully_monomorphized", #[⟨none, sourceType.layoutId, #[]⟩]⟩
    discriminants := some ⟨true, none, (Array.range 3).map fun index => ⟨index, 0, index⟩⟩ }
  let ty := {sourceType with shape := .coroutine definition ownerInstance.genericArgs, compilerFacts := some facts}
  let document := {original with types := original.types.set! 0 ty}
  let source : Miri.Input.SourceInfo := ⟨owner.spanId, 0⟩
  let row : CoroutineEvidence := ⟨0, 0, .Coroutine .Movable, none, none,
    ⟨#[], #[#[], #[], #[]], #[source, source, source], #[]⟩, some 0, none, some 1⟩
  let sync : CoroutineAuxiliaryBody := ⟨0, .sync, .Shim (.DropGlue definition (some 0)),
    {owner with mir := {owner.mir with phase := .Runtime .Initial}}⟩
  let proxy : CoroutineAuxiliaryBody := ⟨0, .proxyAsync, ownerInstance.instanceKind,
    {owner with mir := {owner.mir with phase := .Analysis .PostCleanup}}⟩
  let coverage : CoroutineCoverage := ⟨#[true], #[row], #[sync, proxy]⟩
  let _ ← must (CoroutineCoverageCodec.validate document coverage)
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
  let residualBody : Body := {toBodyCore := residual.toBodyCore, promotedBodies := ownerSeed.promotedBodies}
  invalidCoverage {document with bodies := document.bodies.set! 0 (.material residualBody)} coverage "unlowered terminator"
  invalidCoverage document {coverage with auxiliaryBodies := #[{sync with body := {residual with mir := {residual.mir with phase := .Runtime .Initial}}}, proxy]} "unlowered terminator"
  invalidCoverage document {coverage with auxiliaryBodies := #[{sync with body := {sync.body with definitionId := none}}, proxy]} "auxiliary source kind differs from body definition"
  -- A constructed four-state physical layout: the first three states have no
  -- saved locals; state 3 stores one u8 at offset 1. The root's u8 tag has a
  -- narrowed range, so its query layout deliberately differs from plain u8.
  let some baseLayout := original.layouts[sourceType.layoutId]? | throw (IO.userError "missing fixture layout")
  let some backend := baseLayout.backendRepresentation | throw (IO.userError "missing fixture backend")
  let emptyFields : FieldShape := ⟨.arbitrary, 0, none, none, #[], #[]⟩
  let savedFields : FieldShape := ⟨.arbitrary, 1, none, none, #[1], #[0]⟩
  let rootFields : FieldShape := ⟨.arbitrary, 1, none, none, #[0], #[0]⟩
  let tag : ScalarLayout := ⟨.initialized, ⟨.integer, 1, some (.known .u8), some false, none, none⟩, some (0, 3)⟩
  let variants : Array LayoutVariant := (Array.range 4).map fun index =>
    ⟨(if index == 3 then savedFields else emptyFields), none, index, 2, backend,
      (if index == 3 then #[1] else #[]), false⟩
  let root := {baseLayout with
    fields := some rootFields
    fieldOffsetsBytes := .explicit #[0]
    sizeBytes := some 2
    variantsKind := some .multiple
    variantsLayout := some ⟨.multiple, none, some tag, some ⟨.direct, none, none, none⟩, some 0, variants⟩
    randomizationSeed := 43}
  let selected := (Array.range 4).map fun index => {root with
    fields := some (if index == 3 then savedFields else emptyFields)
    fieldOffsetsBytes := .explicit (if index == 3 then #[1] else #[])
    variantsKind := some .single
    variantsLayout := some ⟨.single, some index, none, none, none, #[]⟩
    randomizationSeed := 0}
  let tagLayout := {baseLayout with
    sizeBytes := some 1
    backendReprKind := some .scalar
    backendRepresentation := some ⟨.scalar, none, some tag, none, none, none, none, none, none⟩}
  let rootId := original.layouts.size
  let tagId := rootId + 5
  let parents : Array ProjectionParent := #[⟨none, rootId, #[⟨0, 1, tagId⟩]⟩] ++
    (Array.range 4).map fun index => ⟨some index, rootId + index + 1,
      (if index == 3 then #[⟨0, 1, 1⟩] else #[])⟩
  let multiFacts := {facts with
    projectionQueries := some ⟨"fully_monomorphized", parents⟩
    discriminants := some ⟨true, none, (Array.range 4).map fun index => ⟨index, 0, index⟩⟩}
  let multiType := {ty with layoutId := rootId, compilerFacts := some multiFacts}
  let multiDocument := {document with
    layouts := original.layouts ++ #[root] ++ selected ++ #[tagLayout]
    types := document.types.set! 0 multiType}
  let multiRow := {row with layout := ⟨#[⟨1, source, false, none⟩],
    #[#[], #[], #[], #[0]], #[source, source, source, source], #[#[]]⟩}
  let multiCoverage := {coverage with coroutines := #[multiRow]}
  let _ ← must (CoroutineCoverageCodec.validate multiDocument multiCoverage)
  let some stateParent := parents[4]? | throw (IO.userError "missing state query")
  let some stateLayout := selected[3]? | throw (IO.userError "missing selected layout")
  let wrongSize := {stateLayout with sizeBytes := some 3}
  let badId := multiDocument.layouts.size
  let wrongParents := parents.set! 4 {stateParent with layoutId := badId}
  let wrongFacts := {multiFacts with projectionQueries := some ⟨"fully_monomorphized", wrongParents⟩}
  let wrongType := {multiType with compilerFacts := some wrongFacts}
  let wrongDocument := {multiDocument with
    layouts := multiDocument.layouts.push wrongSize
    types := multiDocument.types.set! 0 wrongType}
  invalidCoverage wrongDocument multiCoverage "selected query differs from exact physical variant"
  let wrongOffset := {stateLayout with fields := some rootFields, fieldOffsetsBytes := .explicit #[0]}
  invalidCoverage {wrongDocument with layouts := wrongDocument.layouts.set! badId wrongOffset}
    multiCoverage "selected query differs from exact physical variant"
  let phantomParent := {stateParent with fields := #[⟨0, 1, tagId⟩]}
  let phantomFacts := {multiFacts with projectionQueries := some ⟨"fully_monomorphized", parents.set! 4 phantomParent⟩}
  let phantomType := {multiType with compilerFacts := some phantomFacts}
  invalidCoverage {multiDocument with types := multiDocument.types.set! 0 phantomType}
    multiCoverage "saved field query layout differs from exact type layout"
  IO.println "PASS constructed coroutine ownership/type/index/conflict/phase/role/residual negatives"

/-- Finite decoder contract checks. The fixed schema-11 input is read, never
rewritten; schema-13 test adaptations exist only in memory and establish no guest safety. -/
def main : IO Unit := do
  let legacy ← IO.FS.readFile "examples/empty_function/input.json"
  rejected legacy "unsupported schema version"
  let raw ← must (JsonFixtures.parse legacy)
  let count := (← must ((← must (raw.field "bodies")).array)).size
  let markers := "[" ++ String.intercalate "," (List.replicate count "false") ++ "]"
  let catalog := object [("body_coroutines", markers), ("coroutines", "[]"), ("auxiliary_bodies", "[]")]
  let adapted ← must (adaptLegacyFixture legacy)
  let newVersion ← must (withoutField adapted "compiler_coroutine_coverage")
  let valid ← must (setField newVersion "compiler_coroutine_coverage" catalog)
  let newDecoded ← must (decodeJson valid)
  check newDecoded.document.coroutineCoverage.isSome "schema 13 failed to retain typed coverage"
  let current ← must (JsonFixtures.parse valid)
  let bodies ← must ((← must (current.field "bodies")).array)
  let some first := bodies[0]? | throw (IO.userError "current fixture body missing")
  let missingKind ← must (withoutField first.text "body_kind")
  let missingKindBodies := bodies.map (·.text) |>.set! 0 missingKind
  let missingKindBodies := "[" ++ String.intercalate "," missingKindBodies.toList ++ "]"
  rejected (← must (setField valid "bodies" missingKindBodies)) "body_kind"
  rejected (← must (withoutField valid "mir_templates")) "mir_templates"
  rejected (← must (withoutField valid "compiler_instance_abis")) "compiler_instance_abis"
  -- Fixture edits reorder root fields. Put the obsolete header first so this
  -- control tests version rejection before interpreting obsolete body fields.
  let legacyCatalog ← must (setField legacy "compiler_coroutine_coverage" catalog)
  rejected (← must (setField legacyCatalog "schema_version" "11")) "unsupported schema version"
  rejected newVersion "schema 13 requires"
  rejected (← must (setField valid "schema_version" "12")) "unsupported schema version"
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
    pure pools) legacy)
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
  componentChecks newDecoded.document
  IO.println "PASS strict schema-13 coroutine coverage, retained evidence and malformed/missing/unknown guards"
