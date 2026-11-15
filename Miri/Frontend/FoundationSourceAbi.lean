import Miri.Frontend.FoundationSourceSymbolNames
import Miri.Frontend.Foundation
import Miri.Frontend.FoundationSourceTypes
import Miri.Input.Model.SourceAbi

/-! One-time ingestion of ABI declaration syntax. JSON is discarded after this
conversion; runtime ABI demands consume only the typed SourceAbi records. -/
namespace Miri.Frontend.Foundation.SourceAbiParser
open Lean Miri
open Input.SourceAbi
private def raw (document : Document) (definition : Nat) : Except String Input.DefinitionId := do
  let some row := document.definitions[definition]? | throw "ABI source definition absent"
  unless (← row.getObjValAs? Nat "definition_id") == definition do throw "ABI source definition index mismatch"
  return ⟨← row.getObjValAs? Nat "crate_index",← row.getObjValAs? Nat "index"⟩
private def role (name : String) : Except String BuiltinTrait := do
  match name with
  | "sized" => pure .sized | "copy" => pure .copy | "meta_sized" => pure .metaSized
  | _ => throw "unknown ABI builtin language-item role"
def declaration (document : Document) (clause : Json) : Except String (Clause × Option BuiltinDeclaration) := do
  match ← clause.getObjValAs? String "kind" with
  | "trait" =>
    let definition ← raw document (← clause.getObjValAs? Nat "definition")
    let mut arguments : Array Input.SourceTypes.TypeRef := #[]
    for argument in (← clause.getObjValAs? (Array Json) "arguments") do
      unless (← argument.getObjValAs? String "kind") == "type" do
        return (.unsupported "non-type trait argument",none)
      arguments := arguments.push (← argument.getObjValAs? Nat "type")
    let sourceRole ← match clause.getObjVal? "lang_item" with
      | .error _ | .ok .null => pure none
      | .ok source => do
        let name ← source.getStr?
        pure (some (← role name))
    let builtin ← match sourceRole with
      | none => pure none
      | some kind =>
        let pinned ← clause.getObjValAs? Bool "pinned_core_builtin"
        pure (some (BuiltinDeclaration.mk definition kind pinned))
    return (.trait definition sourceRole arguments,builtin)
  | "projection" =>
    unless (← clause.getObjValAs? (Array Json) "bound_variables").isEmpty do return (.unsupported "bound projection",none)
    let term ← clause.getObjVal? "term"
    unless (← term.getObjValAs? String "kind") == "type" do return (.unsupported "const projection",none)
    let arguments ← (← clause.getObjValAs? (Array Json) "arguments").mapM fun argument => do
      unless (← argument.getObjValAs? String "kind") == "type" do throw "ABI projection non-type argument"
      argument.getObjValAs? Nat "type"
    return (.projection (← raw document (← clause.getObjValAs? Nat "definition"))
      (← raw document (← clause.getObjValAs? Nat "parent_trait")) arguments (← term.getObjValAs? Nat "type"),none)
  | "type_outlives" =>
    return (.typeOutlives (← clause.getObjValAs? Nat "type") (← SourceTypesParser.region (← clause.getObjVal? "region")),none)
  | "region_outlives" =>
    return (.regionOutlives (← SourceTypesParser.region (← clause.getObjVal? "longer"))
      (← SourceTypesParser.region (← clause.getObjVal? "shorter")),none)
  | "const_has_type" =>
    let value ← clause.getObjVal? "value"
    if (← value.getObjValAs? String "kind") != "param" then return (.unsupported "non-parameter const typing clause",none)
    return (.constHasType (← value.getObjValAs? Nat "index") (← clause.getObjValAs? Nat "type"),none)
  | other => pure (.unsupported other,none)

private def ordinaryTraits (document : Document) : Except String (Array TraitDeclaration × Array BuiltinDeclaration) := do
  let source ← document.source.getObjVal? "termination_source"
  if source == Json.null then return (#[],#[])
  let definition ← raw document (← source.getObjValAs? Nat "definition")
  let parent ← (← source.getObjValAs? (Option Nat) "generic_parent").mapM (raw document)
  let mut supers := #[]
  for clause in (← source.getObjValAs? (Array Json) "super_clauses") do
    unless (← clause.getObjValAs? String "kind") == "trait" do throw "ordinary trait super-clause encoding unsupported"
    supers := supers.push (SuperTrait.mk (← raw document (← clause.getObjValAs? Nat "definition"))
      (← clause.getObjValAs? Nat "argument_count") (← clause.getObjValAs? (Option Nat) "self_parameter")
      ((← clause.getObjValAs? String "polarity") == "Positive") (← clause.getObjValAs? Nat "bound_variable_count"))
  let mut implementations := #[]
  for header in (← source.getObjValAs? (Array Json) "implementations") do
    let head ← header.getObjVal? "self_constructor"
    let head : SelfHead ← match ← head.getObjValAs? String "kind" with
      | "tuple" => SelfHead.tuple <$> head.getObjValAs? Nat "arity"
      | "never" => pure SelfHead.never
      | "adt" => do
        let crate ← head.getObjValAs? Nat "crate_index"
        let index ← head.getObjValAs? Nat "index"
        pure (SelfHead.adt ⟨crate,index⟩)
      | tag => pure (SelfHead.unsupported tag)
    implementations := implementations.push (ImplHeader.mk (← raw document (← header.getObjValAs? Nat "definition"))
      (← raw document (← header.getObjValAs? Nat "trait_definition")) (← header.getObjValAs? Nat "argument_count") head
      (← header.getObjValAs? Nat "parameter_count") (← (← header.getObjValAs? (Option Nat) "generic_parent").mapM (raw document))
      (← header.getObjValAs? Nat "clause_count") (← (← header.getObjValAs? (Option Nat) "clause_parent").mapM (raw document))
      ((← header.getObjValAs? String "polarity") == "Positive") ((← header.getObjValAs? String "constness") == "NotConst")
      (← header.getObjValAs? Bool "final"))
  let declaration := TraitDeclaration.mk definition (← source.getObjValAs? Bool "auto")
    (← source.getObjValAs? Bool "marker") (← source.getObjValAs? Bool "coinductive")
    ((← source.getObjValAs? String "safety") == "Safe") ((← source.getObjValAs? String "constness") == "NotConst")
    (← source.getObjValAs? Nat "parameter_count") (← source.getObjValAs? Bool "has_self") parent
    (← source.getObjValAs? Bool "complete_impl_headers") supers implementations
  let metadataDefinition ← source.getObjValAs? (Option Nat) "meta_sized_definition"
  let builtins ← metadataDefinition.toArray.mapM fun id => do
    let pinned ← match source.getObjValAs? Bool "meta_sized_core_source" with | .ok value => pure value | .error _ => pure false
    return BuiltinDeclaration.mk (← raw document id) .metaSized pinned
  return (#[declaration],builtins)

/-- Validate the pinned callable declarations once. The compact typed record
retains identities only after all generic declaration obligations are checked. -/
private def callableDeclarations (document : Document) : Except String (Array CallableDeclaration) := do
  let source ← document.source.getObjVal? "fn_vtable_source"
  if source == Json.null then return #[]
  let declarations ← source.getObjValAs? (Array Json) "declarations"
  -- Older source envelopes lack full declaration clauses, so provide no callable capability.
  if declarations.any (fun row => (row.getObjVal? "clause_source").toOption.isNone) then return #[]
  let roots ← source.getObjValAs? (Array Json) "roots"
  let root (name : String) : Except String Nat := do
    let [row] := (roots.filter fun row => (row.getObjValAs? String "kind").toOption == some name).toList
      | throw "ABI callable root absent/ambiguous"
    row.getObjValAs? Nat "definition"
  let fnId ← root "fn"
  let mutId ← root "fn_mut"
  let onceId ← root "fn_once"
  let named (name : String) : Except String Nat := do
    let [row] := (declarations.filter fun row => (row.getObjValAs? String "lang_item").toOption == some name).toList
      | throw "ABI callable declaration absent/ambiguous"
    row.getObjValAs? Nat "definition"
  let metadataId ← named "meta_sized"
  let mut result := #[]
  for (id, name, kind, parent) in #[(fnId,"fn",CallableKind.fn,some mutId),
      (mutId,"fn_mut",CallableKind.fnMut,some onceId),(onceId,"fn_once",CallableKind.fnOnce,none)] do
    let [row] := (declarations.filter fun row => (row.getObjValAs? Nat "definition").toOption == some id).toList
      | throw "ABI callable declaration identity ambiguous"
    unless (← row.getObjValAs? Bool "core_source") && (← row.getObjValAs? Bool "has_self") &&
        (← row.getObjValAs? String "lang_item") == name do throw "ABI callable declaration role mismatch"
    let parameters ← row.getObjValAs? (Array Json) "parameters"
    unless parameters.size == 2 do throw "ABI callable generic arity unsupported"
    for (parameter,index) in parameters.zip #[0,1] do
      unless (← parameter.getObjValAs? Nat "index") == index &&
          (← parameter.getObjValAs? String "kind") == "type" && !(← parameter.getObjValAs? Bool "has_default") do
        throw "ABI callable generic declaration unsupported"
    let owners ← row.getObjValAs? (Array Json) "clause_source"
    let [owner] := owners.toList | throw "ABI callable lexical clauses unsupported"
    unless (← owner.getObjValAs? Nat "definition") == id && (← owner.getObjVal? "parent") == Json.null do
      throw "ABI callable clause owner mismatch"
    let mut observed : Array (String × Array Nat) := #[]
    for clause in (← owner.getObjValAs? (Array Json) "clauses") do
      unless (← clause.getObjValAs? String "kind") == "trait" &&
          (← clause.getObjValAs? Bool "core_source") && (← clause.getObjValAs? String "polarity") == "Positive" &&
          (← clause.getObjValAs? (Array Json) "bound_variables").isEmpty do throw "ABI callable clause unsupported"
      let role ← clause.getObjValAs? String "lang_item"
      let target ← clause.getObjValAs? Nat "definition"
      let expectedId ← match role with
        | "fn" => pure fnId | "fn_mut" => pure mutId | "fn_once" => pure onceId
        | "meta_sized" => pure metadataId
        | "sized" | "tuple" => pure target
        | _ => throw "ABI callable clause language role unsupported"
      unless target == expectedId do throw "ABI callable clause identity mismatch"
      let arguments ← (← clause.getObjValAs? (Array Json) "arguments").mapM fun argument => do
        unless (← argument.getObjValAs? String "kind") == "type" do throw "ABI callable argument unsupported"
        let type ← argument.getObjVal? "type"
        unless (← type.getObjValAs? String "kind") == "param" do throw "ABI callable type template unsupported"
        type.getObjValAs? Nat "index"
      observed := observed.push (role,arguments)
    let expected := #[("meta_sized",#[0]),("sized",#[1]),("tuple",#[1]),(name,#[0,1])] ++
      (if parent == some mutId then #[("fn_mut",#[0,1])] else if parent == some onceId then #[("fn_once",#[0,1])] else #[])
    unless observed.size == expected.size && expected.all (fun value => (observed.filter (· == value)).size == 1) do
      throw "ABI callable declaration conditions unsupported"
    let mut output := none
    for item in (← row.getObjValAs? (Array Json) "associated_items") do
      if ((item.getObjValAs? (Option String) "lang_item").toOption.bind fun value => value) == some "fn_once_output" then
        unless kind == .fnOnce && output.isNone && (← item.getObjValAs? String "kind") == "type" do
          throw "ABI callable Output identity unsupported"
        output := some (← raw document (← item.getObjValAs? Nat "definition"))
    unless (kind == .fnOnce) == output.isSome do throw "ABI callable Output declaration absent"
    result := result.push ⟨← raw document id,kind,output⟩
  return result

/-- Retain the full declaration graph already captured by the producer. No
instantiated bound, selected object candidate, or query answer is stored. -/
private def objectTraitDeclarations (document : Document) : Except String (Array ObjectTraitDeclaration) := do
  let source ← document.source.getObjVal? "fn_vtable_source"
  if source == Json.null then return #[]
  let mut result := #[]
  for row in (← source.getObjValAs? (Array Json) "declarations") do
    let definition ← raw document (← row.getObjValAs? Nat "definition")
    unless !(result.any (fun (old : ObjectTraitDeclaration) => old.definition == definition)) do
      throw "object trait declaration identity duplicated"
    let clauses ← row.getObjValAs? (Array Json) "super_clauses"
    let mut superTraits := #[]
    let mut unsupported := #[]
    for clause in clauses do
      let kind ← clause.getObjValAs? String "kind"
      if kind == "trait" then
        superTraits := superTraits.push (← raw document (← clause.getObjValAs? Nat "definition"))
      else unsupported := unsupported.push kind
    result := result.push ⟨definition,superTraits,unsupported⟩
  return result

private def targetFeatures (row : Json) : Except String (Array TargetFeature) := do
  (← (← row.getObjVal? "runtime_source").getObjValAs? (Array Json) "target_features").mapM fun feature => do
    let name ← feature.getObjValAs? String "name"
    unless !name.isEmpty do throw "empty source target-feature name"
    let kind ← match ← feature.getObjValAs? String "kind" with
      | "Enabled" => pure TargetFeatureKind.enabled
      | "Forced" => pure .forced
      | "Implied" => pure .implied
      | tag => pure (.unsupported tag)
    return TargetFeature.mk name kind

/-- Preserve every captured source header and lexical clause owner exactly once.
No concrete substitutions, ABI results or selected implementations are produced. -/
private def autoTraits (document : Document) : Except String (Option AutoTraits) := do
  let source ← document.source.getObjVal? "closure_auto_source"
  let langs ← match source.getObjVal? "lang_items" with
    | .ok value => pure value
    | .error _ => return none
  let mut langItems := #[]
  for (name,role) in #[("unpin",AutoTraitRole.unpin),("unsafe_unpin",.unsafeUnpin),("freeze",.freeze)] do
    let value ← langs.getObjVal? name
    let id : Option Nat ← fromJson? value
    langItems := langItems.push (role,← id.mapM (raw document))
  let rawId (source : Json) : Except String Input.DefinitionId := do
    let crate ← source.getObjValAs? Nat "crate_index"
    let index ← source.getObjValAs? Nat "index"
    unless crate < 2^32 && index < 2^32 do throw "auto trait raw definition exceeds rustc width"
    return ⟨crate,index⟩
  let identities := langItems.filterMap (·.2)
  unless identities.toList.eraseDups.length == identities.size do throw "auto trait language identities duplicated"
  let mut declarations := #[]
  for row in (← source.getObjValAs? (Array Json) "declarations") do
    let definition ← raw document (← row.getObjValAs? Nat "definition")
    unless !(declarations.any (fun (entry : AutoDeclaration) => entry.definition == definition)) do
      throw "auto trait declaration duplicated"
    let langSource ← row.getObjVal? "lang_item"
    let langTag : Option String ← fromJson? langSource
    let langItem ← langTag.mapM fun tag => match tag with
      | "unpin" => pure AutoTraitRole.unpin
      | "unsafe_unpin" => pure .unsafeUnpin
      | "freeze" => pure .freeze
      | _ => throw "auto trait language role unknown"
    let safety ← row.getObjValAs? String "safety"
    unless safety == "Safe" || safety == "Unsafe" do throw "auto trait safety source unknown"
    let parameters ← (← row.getObjValAs? (Array Json) "parameters").mapM fun parameter => do
      unless (← parameter.getObjValAs? String "kind") == "type" do throw "auto trait parameter source unsupported"
      return (← parameter.getObjValAs? Nat "index",← parameter.getObjValAs? Bool "has_default")
    let clauses ← (← row.getObjValAs? (Array Json) "clauses").mapM fun clause => do
      if (← clause.getObjValAs? String "kind") == "meta_sized_self" then
        return Except.ok (← raw document (← clause.getObjValAs? Nat "definition"))
      pure (Except.error "auto trait super-clause unsupported")
    let implementations ← (← row.getObjValAs? (Array Json) "manual_impl_headers").mapM fun header => do
      let head ← header.getObjVal? "self_constructor"
      let rec parseHead (fuel : Nat) (head : Json) : Except String AutoSelfHead := do
        let .succ fuel := fuel | throw "auto impl outer pattern nesting unsupported"
        match ← head.getObjValAs? String "kind" with
        | "pattern" => return .pattern (← parseHead fuel (← head.getObjVal? "base")) (← head.getObjValAs? String "pattern_kind")
        | "adt" => AutoSelfHead.adt <$> (rawId (← head.getObjVal? "definition"))
        | "fn_def" => AutoSelfHead.functionDefinition <$> (rawId (← head.getObjVal? "definition"))
        | "closure" => AutoSelfHead.closure <$> (rawId (← head.getObjVal? "definition"))
        | "coroutine_closure" => AutoSelfHead.coroutineClosure <$> (rawId (← head.getObjVal? "definition"))
        | "tuple" => AutoSelfHead.tuple <$> head.getObjValAs? Nat "arity"
        | "unknown" => pure AutoSelfHead.unknown
        | tag =>
          if #["fn_pointer","raw_pointer","reference","array","slice","str","bool","char","int","uint","float","never","dynamic"].contains tag
          then pure (.rigid tag) else throw "auto impl outer constructor unknown"
      let selfHead ← parseHead 256 head
      let polarity ← header.getObjValAs? String "polarity"
      unless #["Positive","Negative","Reservation"].contains polarity do throw "auto impl polarity unknown"
      return AutoImplHeader.mk (← rawId (← header.getObjVal? "definition")) selfHead polarity
    declarations := declarations.push (AutoDeclaration.mk definition langItem (← row.getObjValAs? Bool "is_auto")
      (safety == "Unsafe") (← row.getObjValAs? Bool "has_self") parameters
      (← row.getObjValAs? Nat "associated_item_count") clauses
      (← row.getObjValAs? Bool "complete_manual_headers") implementations)
  return some ⟨langItems,declarations⟩

def material (document : Document) : Except String Material := do
  let compilation ← document.source.getObjVal? "compilation"
  let panic ← compilation.getObjValAs? String "panic_strategy"
  let drop ← compilation.getObjValAs? String "panic_in_drop"
  unless (panic == "abort" || panic == "unwind") && (drop == "abort" || drop == "unwind") do
    throw "ABI source panic strategy invalid"
  let headers ← document.source.getObjValAs? (Array Json) "source_function_signatures"
  let mut rows := document.bodies
  for header in headers do
    let definition ← header.getObjValAs? Nat "definition"
    let matching := rows.filter fun row => (row.getObjValAs? Nat "definition").toOption == some definition
    if let some body := matching[0]? then
      unless matching.size == 1 do throw "duplicate ABI source body owner"
      for field in #["environment","signature","function_attributes"] do
        unless (← body.getObjVal? field) == (← header.getObjVal? field) do throw "conflicting ABI source signature/header"
      unless (← (← body.getObjVal? "runtime_source").getObjVal? "target_features") ==
          (← (← header.getObjVal? "runtime_source").getObjVal? "target_features") do
        throw "conflicting declaration target-feature source"
    else rows := rows.push header
  let mut targetFeatureDeclarations : Array TargetFeatureDeclaration := #[]
  let mut functions : Array Function := #[]
  let mut owners : Array OwnerClauses := #[]
  let mut builtins : Array BuiltinDeclaration := #[]
  for row in rows do
    let definition ← raw document (← row.getObjValAs? Nat "definition")
    unless !(functions.any fun f => f.definition == definition) do throw "duplicate ABI function declaration"
    let signature ← SourceTypesParser.signature (← row.getObjVal? "signature")
    unless signature.output < document.types.size && signature.inputs.all (· < document.types.size) do throw "ABI signature source type reference absent"
    let attrs ← row.getObjVal? "function_attributes"
    targetFeatureDeclarations := targetFeatureDeclarations.push ⟨definition,← targetFeatures row⟩
    let attributes : Attributes := ⟨← attrs.getObjValAs? Bool "never_unwind",← attrs.getObjValAs? Bool "track_caller",
      ← attrs.getObjValAs? Bool "is_foreign",← attrs.getObjValAs? Bool "is_drop_glue"⟩
    let environment ← row.getObjVal? "environment"
    unless (← raw document (← environment.getObjValAs? Nat "owner")) == definition do throw "ABI source environment owner mismatch"
    let mut parameters : Array ConstParameterType := #[]
    for layer in (← environment.getObjValAs? (Array Json) "layers") do
      let owner ← raw document (← layer.getObjValAs? Nat "owner")
      let parent ← (← layer.getObjValAs? (Option Nat) "parent").mapM (raw document)
      let mut clauses := #[]
      for clause in (← layer.getObjValAs? (Array Json) "clauses") do
        let (clause,builtin) ← declaration document clause
        clauses := clauses.push clause
        if let some builtin := builtin then
          if let some existing := builtins.find? (·.definition == builtin.definition) then
            unless existing == builtin do throw "conflicting builtin source declaration role"
          else builtins := builtins.push builtin
      let source := OwnerClauses.mk owner parent clauses
      if let some existing := owners.find? (·.owner == owner) then
        unless existing == source do throw "conflicting ABI lexical clauses"
      else owners := owners.push source
      for parameter in (← layer.getObjValAs? (Array Json) "parameters") do
        if (← parameter.getObjValAs? String "kind") == "const" then
          parameters := parameters.push (ConstParameterType.mk (← raw document (← parameter.getObjValAs? Nat "definition"))
            (← parameter.getObjValAs? Nat "type"))
    functions := functions.push (Function.mk definition signature attributes parameters)
  for row in (← document.source.getObjValAs? (Array Json) "closure_templates") do
    -- A closure declaration is not an ordinary function signature. Missing
    -- attribute material supplies no row and remains unavailable at demand.
    if (row.getObjVal? "runtime_source").isOk then
      let definition ← raw document (← row.getObjValAs? Nat "definition")
      let features ← targetFeatures row
      if let some old := targetFeatureDeclarations.find? (·.definition == definition) then
        unless old.features == features do throw "conflicting closure target-feature source"
      else targetFeatureDeclarations := targetFeatureDeclarations.push ⟨definition,features⟩
  let (traits,extraBuiltins) ← ordinaryTraits document
  for declaration in extraBuiltins do
    if let some existing := builtins.find? (·.definition == declaration.definition) then
      unless existing == declaration do throw "conflicting ordinary trait builtin declaration"
    else builtins := builtins.push declaration
  let callerIncremental ← match compilation.getObjVal? "incremental" with
    | .error _ => pure none | .ok value => fromJson? value
  return ⟨functions,owners,builtins,panic == "unwind",drop == "unwind",traits,← callableDeclarations document,← autoTraits document,(← compilation.getObjValAs? String "opt_level") == "No",← objectTraitDeclarations document,← SourceSymbolNamesParser.material document,targetFeatureDeclarations,callerIncremental⟩
end Miri.Frontend.Foundation.SourceAbiParser
