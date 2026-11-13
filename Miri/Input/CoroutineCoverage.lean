import Miri.Input.Model
import Miri.Input.DecodeMIR
import Miri.Input.RuntimeMetadata
import Miri.Input.GenericMaterialCodec
import Miri.Input.CoroutineGenericSource

namespace Miri.Input.CoroutineCoverageCodec
open JsonReader

private def role : Parser CoroutineAuxiliaryRole := do
  match ← string with
  | "sync" => pure .sync
  | "async" => pure .async
  | "proxy_async" => pure .proxyAsync
  | _ => fail "unknown coroutine auxiliary role"

private structure KindFields where
  kind : Option String := none
  desugaring : Option String := none
  source : Option String := none
  movability : Option String := none

private def kind : Parser Miri.MIR.CoroutineKind := do
  let v ← object ({} : KindFields) fun v key => do
    match key with
    | "kind" => return {v with kind := some (← string)}
    | "desugaring" => return {v with desugaring := some (← string)}
    | "source" => return {v with source := some (← string)}
    | "movability" => return {v with movability := some (← string)}
    | _ => fail s!"unknown coroutine kind field `{key}`"
  match ← required v.kind "kind" with
  | "coroutine" =>
    unless v.desugaring.isNone && v.source.isNone do fail "incompatible coroutine kind fields"
    match ← required v.movability "movability" with
    | "static" => pure (.Coroutine .Static)
    | "movable" => pure (.Coroutine .Movable)
    | _ => fail "unknown coroutine movability"
  | "desugared" =>
    unless v.movability.isNone do fail "incompatible coroutine kind fields"
    let desugaring ← match ← required v.desugaring "desugaring" with
      | "async" => pure Miri.MIR.CoroutineDesugaring.Async
      | "gen" => pure .Gen
      | "async_gen" => pure .AsyncGen
      | _ => fail "unknown coroutine desugaring"
    let source ← match ← required v.source "source" with
      | "block" => pure Miri.MIR.CoroutineSource.Block
      | "closure" => pure .Closure
      | "function" => pure .Fn
      | _ => fail "unknown coroutine source"
    pure (.Desugared desugaring source)
  | _ => fail "unknown coroutine kind"

private structure SourceFields where
  span : Option Nat := none
  scope : Option Nat := none
private def sourceInfo : Parser SourceInfo := do
  let v ← object ({} : SourceFields) fun v key => do
    match key with
    | "span" => return {v with span := some (← natural)}
    | "scope" => return {v with scope := some (← natural)}
    | _ => fail s!"unknown coroutine source-info field `{key}`"
  pure ⟨(← required v.span "span"), (← required v.scope "scope")⟩

private structure SourceKindFields where
  kind : Option String := none
  shim : Option String := none
  definition : Option Nat := none
  dropType : Option (Option Nat) := none
  coroutineType : Option Nat := none
private def sourceKind : Parser Miri.Interpreter.CallInstanceKind := do
  let v ← object ({} : SourceKindFields) fun v key => do
    match key with
    | "kind" => return {v with kind := some (← string)}
    | "shim_kind" => return {v with shim := some (← string)}
    | "def_id" => return {v with definition := some (← natural)}
    | "drop_type" => return {v with dropType := some (← nullable natural)}
    | "coroutine_type" => return {v with coroutineType := some (← natural)}
    | _ => fail s!"unknown coroutine source-kind field `{key}`"
  let definition ← required v.definition "def_id"
  match ← required v.kind "kind" with
  | "item" =>
    unless v.shim.isNone && v.dropType.isNone && v.coroutineType.isNone do fail "incompatible coroutine Item source"
    pure (.Item definition)
  | "shim" =>
    match ← required v.shim "shim_kind" with
    | "drop_glue" =>
      unless v.coroutineType.isNone do fail "incompatible coroutine DropGlue source"
      pure (.Shim (.DropGlue definition (← required v.dropType "drop_type")))
    | "async_drop_glue" =>
      unless v.dropType.isNone do fail "incompatible coroutine AsyncDropGlue source"
      pure (.Shim (.AsyncDropGlue definition (← required v.coroutineType "coroutine_type")))
    | _ => fail "unknown coroutine source shim"
  | _ => fail "unknown coroutine source kind"

private def sharedSource (pools : DecodeMIR.MIRParser.SharedPools) : Parser SourceInfo := do
  let reference ← natural
  let some value := pools.sources[reference]? | fail "coroutine coverage: dangling source-info pool reference"
  pure value

private structure fieldFields (Child : Type) where
  type : Option Child := none
  source_info : Option (SourceInfo) := none
  ignore_for_traits : Option (Bool) := none
  debuginfo_name : Option (Option String) := none

private def field (pools : DecodeMIR.MIRParser.SharedPools) (child : Parser Child) : Parser (CoroutineSavedField Child) := do
  let v ← object ({} : fieldFields Child) fun v key => do
    match key with
    | "type" => return {v with type := some (← child)}
    | "source_info" => return {v with source_info := some (← sharedSource pools)}
    | "ignore_for_traits" => return {v with ignore_for_traits := some (← boolean)}
    | "debuginfo_name" => return {v with debuginfo_name := some (← nullable string)}
    | _ => fail s!"unknown coroutine coverage field `{key}`"
  return ⟨(← required v.type "type"), (← required v.source_info "source_info"), (← required v.ignore_for_traits "ignore_for_traits"), (← required v.debuginfo_name "debuginfo_name")⟩

private structure layoutFields (Child : Type) where
  field_tys : Option (Array (CoroutineSavedField Child)) := none
  variant_fields : Option (Array (Array Nat)) := none
  variant_source_info : Option (Array SourceInfo) := none
  storage_conflicts : Option (Array (Array Nat)) := none

private def layout (pools : DecodeMIR.MIRParser.SharedPools) (child : Parser Child) : Parser (CoroutineLayoutEvidence Child) := do
  let v ← object ({} : layoutFields Child) fun v key => do
    match key with
    | "field_tys" => return {v with field_tys := some (← array (field pools child))}
    | "variant_fields" => return {v with variant_fields := some (← array (array natural))}
    | "variant_source_info" => return {v with variant_source_info := some (← array sourceInfo)}
    | "storage_conflicts" => return {v with storage_conflicts := some (← array (array natural))}
    | _ => fail s!"unknown coroutine coverage field `{key}`"
  return ⟨(← required v.field_tys "field_tys"), (← required v.variant_fields "variant_fields"), (← required v.variant_source_info "variant_source_info"), (← required v.storage_conflicts "storage_conflicts")⟩

private structure evidenceFields where
  owner_body : Option (Nat) := none
  coroutine_type : Option (Nat) := none
  coroutine_kind : Option (Miri.MIR.CoroutineKind) := none
  yield_type : Option (Option Nat) := none
  resume_type : Option (Option Nat) := none
  layout : Option (CoroutineLayoutEvidence) := none
  drop_sync : Option (Option Nat) := none
  drop_async : Option (Option Nat) := none
  drop_proxy_async : Option (Option Nat) := none

private def evidence (pools : DecodeMIR.MIRParser.SharedPools) : Parser CoroutineEvidence := do
  let v ← object ({} : evidenceFields) fun v key => do
    match key with
    | "owner_body" => return {v with owner_body := some (← natural)}
    | "coroutine_type" => return {v with coroutine_type := some (← natural)}
    | "coroutine_kind" => return {v with coroutine_kind := some (← kind)}
    | "yield_type" => return {v with yield_type := some (← nullable natural)}
    | "resume_type" => return {v with resume_type := some (← nullable natural)}
    | "layout" => return {v with layout := some (← layout pools natural)}
    | "drop_sync" => return {v with drop_sync := some (← nullable natural)}
    | "drop_async" => return {v with drop_async := some (← nullable natural)}
    | "drop_proxy_async" => return {v with drop_proxy_async := some (← nullable natural)}
    | _ => fail s!"unknown coroutine coverage field `{key}`"
  return ⟨(← required v.owner_body "owner_body"), (← required v.coroutine_type "coroutine_type"), (← required v.coroutine_kind "coroutine_kind"), (← required v.yield_type "yield_type"), (← required v.resume_type "resume_type"), (← required v.layout "layout"), (← required v.drop_sync "drop_sync"), (← required v.drop_async "drop_async"), (← required v.drop_proxy_async "drop_proxy_async")⟩

structure Parsed where
  value : CoroutineCoverage
  references : Array DecodeMIR.References

private structure AuxiliaryFields where
  owner : Option Nat := none
  role : Option CoroutineAuxiliaryRole := none
  sourceKind : Option Miri.Interpreter.CallInstanceKind := none
  body : Option DecodeMIR.ParsedBody := none

private def auxiliary (pools : DecodeMIR.MIRParser.SharedPools) : Parser (CoroutineAuxiliaryBody × DecodeMIR.References) := do
  let v ← object ({} : AuxiliaryFields) fun v key => do
    match key with
    | "owner_body" => return {v with owner := some (← natural)}
    | "role" => return {v with role := some (← role)}
    | "source_kind" => return {v with sourceKind := some (← sourceKind)}
    | "body" => return {v with body := some (← DecodeMIR.parseBody "$coroutine_auxiliary" (some pools))}
    | _ => fail s!"unknown coroutine auxiliary field `{key}`"
  let body ← required v.body "body"
  return (⟨(← required v.owner "owner_body"), (← required v.role "role"),
    (← required v.sourceKind "source_kind"), body.value⟩, body.references)

private def rawJson : Parser Lean.Json := Lean.Json.Parser.anyCore
private def rawTerm : Parser GenericSubstitution.Term := do
  liftExcept (GenericMaterialCodec.readTerm 4096 (← rawJson))
private def rawDefinition : Parser GenericSubstitution.DefinitionIdentity := do
  liftExcept (GenericMaterialCodec.readDefinition (← rawJson))
private def rawSort : Parser GenericSubstitution.ArgSort := do
  liftExcept (GenericMaterialCodec.readSort (← rawJson))

private structure GenericSourceFields where
  owner : Option GenericSubstitution.DefinitionIdentity := none
  physicalOwner : Option GenericSubstitution.DefinitionIdentity := none
  typeckOwner : Option GenericSubstitution.DefinitionIdentity := none
  parentCount : Option Nat := none
  parameters : Option (Array GenericSubstitution.ArgSort) := none
  witnessParameters : Option (Array GenericSubstitution.ArgSort) := none
  typeExpression : Option GenericSubstitution.Term := none
  identityKind : Option GenericSubstitution.Term := none
  byMoveOwner : Option (Option GenericSubstitution.DefinitionIdentity) := none
  layout : Option (CoroutineLayoutEvidence GenericSubstitution.Term) := none

private def genericSource (pools : DecodeMIR.MIRParser.SharedPools) : Parser CoroutineGenericSource := do
  let v ← object ({} : GenericSourceFields) fun v key => do
    match key with
    | "owner" => return {v with owner := some (← rawDefinition)}
    | "physical_owner" => return {v with physicalOwner := some (← rawDefinition)}
    | "typeck_owner" => return {v with typeckOwner := some (← rawDefinition)}
    | "parent_count" => return {v with parentCount := some (← natural)}
    | "parameters" => return {v with parameters := some (← array rawSort)}
    | "witness_parameters" => return {v with witnessParameters := some (← array rawSort)}
    | "type_expression" => return {v with typeExpression := some (← rawTerm)}
    | "identity_kind" => return {v with identityKind := some (← rawTerm)}
    | "by_move_owner" => return {v with byMoveOwner := some (← nullable rawDefinition)}
    | "layout" => return {v with layout := some (← layout pools rawTerm)}
    | _ => fail s!"unknown coroutine generic source field `{key}`"
  return ⟨(← required v.owner "owner"), (← required v.physicalOwner "physical_owner"),
    (← required v.typeckOwner "typeck_owner"), (← required v.parentCount "parent_count"),
    (← required v.parameters "parameters"), (← required v.witnessParameters "witness_parameters"),
    (← required v.typeExpression "type_expression"), (← required v.identityKind "identity_kind"),
    (← required v.byMoveOwner "by_move_owner"), (← required v.layout "layout")⟩

private structure CatalogFields where
  genericSources : Option (Array CoroutineGenericSource) := none
  markers : Option (Array Bool) := none
  coroutines : Option (Array CoroutineEvidence) := none
  auxiliary : Option (Array (CoroutineAuxiliaryBody × DecodeMIR.References)) := none

def parse (pools : DecodeMIR.MIRParser.SharedPools) : Parser Parsed := do
  let v ← object ({} : CatalogFields) fun v key => do
    match key with
    | "generic_sources" => return {v with genericSources := some (← array (genericSource pools))}
    | "body_coroutines" => return {v with markers := some (← array boolean)}
    | "coroutines" => return {v with coroutines := some (← array (evidence pools))}
    | "auxiliary_bodies" => return {v with auxiliary := some (← array (auxiliary pools))}
    | _ => fail s!"unknown coroutine catalog field `{key}`"
  let auxiliary ← required v.auxiliary "auxiliary_bodies"
  return ⟨⟨(← required v.markers "body_coroutines"), (← required v.coroutines "coroutines"), auxiliary.map (·.1), (← required v.genericSources "generic_sources")⟩,
    auxiliary.map (·.2)⟩


private def noResidual (body : Body) : Except String Unit := do
  for block in body.mir.basicBlocks do
    match block.terminator.kind with
    | .Yield .. | .CoroutineDrop | .FalseEdge .. | .FalseUnwind .. =>
      throw "coroutine coverage: unlowered terminator"
    | _ => pure ()

private def sourceBounds (document : ImportDocument) (owner : Body) (info : SourceInfo) : Except String Unit := do
  unless info.spanId < document.spans.size && info.scope < owner.sourceScopes.size do
    throw "coroutine coverage: dangling source info"

/-- Pinned rustc_middle::ty::layout::ty_and_layout_for_variant and
rustc_abi/layout/simple.rs::LayoutData::for_variant. Root attributes are retained;
only the selected physical variant fields and seed are replaced. This validates
query evidence and does not change the runtime's projection implementation. -/
private def physicalVariant (root : Miri.ABI.LayoutData) (index : Nat) : Except String Miri.ABI.LayoutData := do
  match root.variants with
  | .Single actual =>
    unless actual == index do throw "coroutine coverage: invalid single variant query"
    pure root
  | .Multiple _ _ _ variants =>
    let some variant := variants[index]? | throw "coroutine coverage: missing physical variant"
    pure {root with
      fields := .Arbitrary variant.fieldOffsets variant.fieldsInMemoryOrder
      variants := .Single index
      backendRepr := variant.backendRepr
      largestNiche := variant.largestNiche
      uninhabited := variant.uninhabited
      size := variant.size
      randomizationSeed := 0}
  | .Empty => throw "coroutine coverage: unexpected empty variant query"

/-- Validate evidence without ever adding auxiliary bodies to the callable graph. -/
def validate (document : ImportDocument) (coverage : CoroutineCoverage) : Except String Unit := do
  CoroutineGenericSource.validateCatalog coverage.genericSources
  let registered (identity : GenericSubstitution.DefinitionIdentity) :=
    document.definitions.any fun value => value.crateIndex == identity.crateIndex && value.index == identity.index
  for source in coverage.genericSources do
    unless registered source.owner && registered source.physicalOwner && registered source.typeckOwner &&
        source.byMoveOwner.all registered do
      throw "coroutine generic source: declaration identity absent from definition pool"
    for field in source.layout.fields do
      unless field.sourceInfo.spanId < document.spans.size do
        throw "coroutine generic source: dangling saved-field source span"
    for info in source.layout.variantSources do
      unless info.spanId < document.spans.size do
        throw "coroutine generic source: dangling state source span"
  unless coverage.bodyCoroutines.size == document.bodies.size do
    throw "coroutine coverage: incomplete body markers"
  let mut owners : Array Nat := #[]
  let mut auxiliary : Array Nat := #[]
  for row in coverage.coroutines do
    let some seed := document.bodies[row.ownerBody]? |
      throw "coroutine coverage: dangling owner body"
    let .material owner := seed | throw "coroutine coverage: generic copy template cannot be a coroutine owner"
    unless coverage.bodyCoroutines[row.ownerBody]? == some true && !owners.contains row.ownerBody do
      throw "coroutine coverage: missing marker or duplicate owner"
    owners := owners.push row.ownerBody
    match owner.mir.phase with
    | .Runtime _ => pure ()
    | _ => throw "coroutine coverage: executable owner has not reached runtime MIR"
    noResidual owner
    unless row.yieldType.isNone && row.resumeType.isNone do
      throw "coroutine coverage: unlowered yield/resume types"
    let some coroutineType := document.types[row.coroutineType]? |
      throw "coroutine coverage: missing coroutine type"
    let some ownerInstance := document.instances[owner.instanceId]? |
      throw "coroutine coverage: absent owner instance"
    match coroutineType.shape, ownerInstance.instanceKind with
    | .coroutine definition args, .Item source =>
      let some declaration := document.definitions[definition]? |
        throw "coroutine generic source: coroutine owner definition absent"
      unless coverage.genericSources.any (fun value =>
          value.owner.crateIndex == declaration.crateIndex && value.owner.index == declaration.index) do
        throw "coroutine generic source: executable coroutine declaration missing"
      unless definition == source && args == ownerInstance.genericArgs do
        throw "coroutine coverage: coroutine type differs from owner instance"
    | .coroutine .., .Shim (.AsyncDropGlue _ ty) =>
      unless ty == row.coroutineType do throw "coroutine coverage: async glue type differs from owner"
    | _, _ => throw "coroutine coverage: owner type/source is not a coroutine"
    let fields := row.layout.fields
    unless row.layout.variants.size >= 3 && row.layout.variants.size == row.layout.variantSources.size &&
        row.layout.storageConflicts.size == fields.size do
      throw "coroutine coverage: layout dimensions disagree"
    for field in fields do
      unless field.typeId < document.types.size do
        throw "coroutine coverage: dangling saved field type"
      sourceBounds document owner field.sourceInfo
    for info in row.layout.variantSources do sourceBounds document owner info
    for indices in row.layout.variants ++ row.layout.storageConflicts do
      unless indices.all (· < fields.size) && indices.toList.eraseDups.length == indices.size do
        throw "coroutine coverage: invalid or duplicate saved field index"
    -- The source square conflict relation is symmetric. Preserve its exact
    -- sparse rows, including empty rows and diagonal entries.
    for (indices, index) in row.layout.storageConflicts.toList.zipIdx do
      for other in indices do
        let some conflicts := row.layout.storageConflicts[other]? |
          throw "coroutine coverage: invalid or duplicate saved field index"
        unless conflicts.contains index do
          throw "coroutine coverage: asymmetric storage conflicts"
    let some projections := coroutineType.compilerFacts.bind (·.projectionQueries) |
      throw "coroutine coverage: absent exact coroutine projection queries"
    let some discriminants := coroutineType.compilerFacts.bind (·.discriminants) |
      throw "coroutine coverage: missing compiler state discriminants"
    unless discriminants.hasDiscriminants && discriminants.values.size == row.layout.variants.size &&
        (discriminants.values.map (·.variant)) == Array.range row.layout.variants.size do
      throw "coroutine coverage: state discriminants differ from layout variants"
    let some physical := document.layouts[coroutineType.layoutId]? >>= (·.variantsLayout) |
      throw "coroutine coverage: absent physical coroutine variants"
    let some targetEvidence := document.runtimeTargetDataLayout |
      throw "coroutine coverage: missing target data layout"
    let target ← RuntimeMetadata.importTarget targetEvidence |>.mapError toString
    let some _ := document.layouts[coroutineType.layoutId]? |
      throw "coroutine coverage: missing root physical layout"
    let rootLayout ← RuntimeMetadata.resolveLayout target document.types document.layouts coroutineType.layoutId document.definitions document.typeConstants document.predicates |>.mapError toString
    let requiredVariants := if physical.kind == .multiple then physical.variants.size else 0
    unless projections.typingEnvironment == "fully_monomorphized" &&
        projections.parents.size == requiredVariants + 1 &&
        (projections.parents.filter (·.variant.isNone)).size == 1 &&
        ((projections.parents.find? (·.variant.isNone)).map (·.layoutId)) == some coroutineType.layoutId do
      throw "coroutine coverage: incomplete exact projection parents"
    if physical.kind == .multiple then
      unless requiredVariants == row.layout.variants.size &&
          (projections.parents.filterMap (·.variant)) == Array.range requiredVariants do
        throw "coroutine coverage: physical variants differ from state mapping"
    for parent in projections.parents do
      if let some variant := parent.variant then
        let some _ := document.layouts[parent.layoutId]? |
          throw "coroutine coverage: missing selected physical layout"
        let actual ← RuntimeMetadata.resolveLayout target document.types document.layouts parent.layoutId document.definitions document.typeConstants document.predicates |>.mapError toString
        let expected ← physicalVariant rootLayout variant
        unless actual == expected do
          throw "coroutine coverage: selected query differs from exact physical variant"
      let some queryFields := document.layouts[parent.layoutId]? >>= (·.fields) |
        throw "coroutine coverage: absent projection field layout"
      unless queryFields.fieldCount == parent.fields.size do
        throw "coroutine coverage: query fields differ from physical layout"
      unless (parent.fields.map (·.index)) == Array.range parent.fields.size do
        throw "coroutine coverage: field query indices are not canonical"
      let selected := match parent.variant, physical.kind with
        | some variant, _ => some variant
        | none, .single => physical.variantIndex
        | _, _ => none
      if let some variant := selected then
        let some mapping := row.layout.variants[variant]? |
          throw "coroutine coverage: dangling projection variant"
        unless parent.fields.size == mapping.size do
          throw "coroutine coverage: projection/state field count mismatch"
        for (field, index) in parent.fields.toList.zipIdx do
          let some saved := mapping[index]? >>= (fields[·]?) |
            throw "coroutine coverage: missing saved field"
          unless field.typeId == saved.typeId do
            throw "coroutine coverage: projection/saved field type mismatch"
          let some savedType := document.types[saved.typeId]? |
            throw "coroutine coverage: missing saved field type"
          -- Selected state fields use TyMaybeWithLayout::Ty -> layout_of.
          -- Root Multiple's synthetic tag_layout is deliberately not subject
          -- to this canonical type-layout equality (pinned ty/layout.rs:859).
          unless field.layoutId == savedType.layoutId do
            throw "coroutine coverage: saved field query layout differs from exact type layout"
    unless row.dropSync.isSome != row.dropAsync.isSome && row.dropProxyAsync.isSome == row.dropSync.isSome do
      throw "coroutine coverage: inconsistent drop roles"
    for (reference, role) in [(row.dropSync, CoroutineAuxiliaryRole.sync),
        (row.dropAsync, .async), (row.dropProxyAsync, .proxyAsync)] do
      if let some id := reference then
        let some value := coverage.auxiliaryBodies[id]? |
          throw "coroutine coverage: dangling auxiliary body"
        unless value.ownerBody == row.ownerBody && value.role == role && !auxiliary.contains id do
          throw "coroutine coverage: duplicate or mismatched auxiliary role/owner"
        auxiliary := auxiliary.push id
        unless value.body.definitionId == some value.sourceKind.defId do
          throw "coroutine coverage: auxiliary source kind differs from body definition"
        unless value.body.instanceId == owner.instanceId do
          throw "coroutine coverage: auxiliary normalization context differs from owner"
        let validPhase := match role, value.body.mir.phase with
          | .sync, .Runtime .Initial => true
          | .async, .Analysis .PostCleanup | .proxyAsync, .Analysis .PostCleanup => true
          | .async, .Runtime .Initial | .proxyAsync, .Runtime .Initial => true
          | _, _ => false
        unless validPhase do throw "coroutine coverage: unexpected auxiliary snapshot phase"
        noResidual value.body
        match role, value.sourceKind with
        | .sync, .Shim (.DropGlue _ (some ty)) =>
          unless ty == row.coroutineType do throw "coroutine coverage: sync drop type differs from owner"
        | .sync, _ => throw "coroutine coverage: sync drop has no exact DropGlue source"
        | _, sourceKind =>
          let some ownerInstance := document.instances[owner.instanceId]? |
            throw "coroutine coverage: absent owner instance"
          unless sourceKind == ownerInstance.instanceKind do
            throw "coroutine coverage: async/proxy source identity differs from owner"
  unless owners.size == (coverage.bodyCoroutines.filter id).size do
    throw "coroutine coverage: marked body has no witness"
  unless auxiliary.size == coverage.auxiliaryBodies.size do
    throw "coroutine coverage: orphan auxiliary body"

end Miri.Input.CoroutineCoverageCodec
