import Miri.Input.SourceCompilerWorld

/-! Source-backed auto-trait queries for retag. Pinned util.rs trivial fastpaths
are independent of impl selection. A closure is not trivial: selection requires
an auto declaration and complete exclusion of every relevant manual impl, then
recurses through tupled_upvars (select/mod.rs::constituent_types_for_auto_trait).
Unknown or potentially matching headers never become negative evidence. -/
namespace Miri.Input.SourceCompilerAutoTraits
open SourceAbi
abbrev Role := AutoTraitRole
abbrev World := SourceCompilerWorld.World

private def typeNode (world : World) (id : Nat) : Except String TypeNode := do
  let some node := world.canonical.types[id]? | throw "auto trait canonical type absent"
  return node

/-- The exact same trivial fastpath covers Unpin and UnsafeUnpin. Freeze has
this same constructor domain in the pinned compiler. Failure is unknown. -/
private def trivial (world : World) (id : Nat) : Except String Bool := go (world.canonical.types.size+1) id
where
  go (fuel : Nat) (id : Nat) : Except String Bool := do
    let .succ fuel := fuel | throw "auto trait trivial traversal exhausted"
    match (← typeNode world id).shape with
    | .bool | .char | .int _ | .uint _ | .float _ | .str | .never | .reference .. |
      .rawPointer .. | .functionDefinition .. | .functionPointer .. => pure true
    | .array child .. | .slice child | .patternType child _ => go fuel child
    | .tuple fields =>
      for field in fields do unless (← go fuel field) do return false
      pure true
    | _ => pure false

private def abiOfWorld (world : World) : Except String Material := do
  let some source := world.canonical.sourceMaterial | throw "auto trait typed source absent"
  let some abi := source.abi | throw "auto trait declaration source unavailable"
  return abi

private def declaration (abi : Material) (role : Role) : Except String AutoDeclaration := do
  let some material := abi.autoTraits | throw "auto trait language item/header source unavailable"
  let some (_,some definition) := material.langItems.find? (·.1 == role)
    | throw "auto trait language item absent"
  let matching := material.declarations.filter (·.definition == definition)
  let [declaration] := matching.toList | throw "auto trait declaration absent/ambiguous"
  unless declaration.isAuto && declaration.hasSelf && declaration.parameters == #[(0,false)] &&
      declaration.associatedItems == 0 && declaration.complete do
    throw "auto trait source declaration domain unsupported/incomplete"
  unless declaration.langItem == some role do throw "auto trait language identity mismatch"
  for clause in declaration.clauses do
    match clause with
    | .ok _ => pure ()
    | .error reason => throw reason
  return declaration

/-- Exclusion uses only rigid outer constructor identity. A candidate of the
same closure/tuple root or any unknown/alias root needs further selection
material and is Unsupported, including negative and reservation impls. -/
private def outer : AutoSelfHead → AutoSelfHead
  | .pattern base _ => outer base
  | head => head

private def exclude (declaration : AutoDeclaration) (head : AutoSelfHead) : Except String Unit := do
  for implementation in declaration.implementations do
    let disjoint := match outer implementation.selfHead,outer head with
      | .unknown,_ => false
      | .closure a,.closure b => a != b
      | .tuple a,.tuple b => a != b
      | .adt a,.adt b => a != b
      | .functionDefinition a,.functionDefinition b => a != b
      | .coroutineClosure a,.coroutineClosure b => a != b
      | .rigid a,.rigid b => a != b
      | _,_ => true
    unless disjoint do throw "auto trait manual impl may apply; selection source unsupported"

/-- Dyn objects have no structural auto implementation (candidate_assembly.rs
771). Exact explicit auto bounds yield BuiltinObjectCandidate (933); otherwise
exclude the complete principal supertrait declaration closure (958). A reachable
queried declaration needs full argument rebasing, so remains Unsupported here. -/
private def objectBounds (abi : Material) (source : AutoDeclaration)
    (principal : Option DefinitionId) (autoBounds : Array DefinitionId) : Except String Bool := do
  -- Complete relevant manual-impl exclusion is required even when the object
  -- carries an explicit bound; no competing impl is silently discarded.
  exclude source (.rigid "dynamic")
  if autoBounds.contains source.definition then return true
  if let some principalDefinition := principal then
    visit abi source.definition (abi.objectTraits.size+1) #[] principalDefinition
  return false
where
  visit (abi : Material) (target : DefinitionId) (fuel : Nat)
      (active : Array DefinitionId) (definition : DefinitionId) : Except String Unit := do
    unless definition != target do throw "object inherited auto trait requires checked argument rebasing"
    unless !active.contains definition do throw "object supertrait cycle unsupported"
    let .succ fuel := fuel | throw "object supertrait traversal exhausted"
    let [row] := (abi.objectTraits.filter (·.definition == definition)).toList
      | throw "object supertrait declaration absent/ambiguous"
    unless row.unsupportedSuperClauses.isEmpty do throw "object supertrait graph unsupported"
    for parent in row.superTraits do
      visit abi target fuel (active.push definition) parent

/-- The same object rule over a minimal typed goal, usable before canonical
physical interning. Trait arguments are unnecessary for a negative DefId proof;
a reachable queried role still rejects until positive rebasing is available. -/
def checkObjectBounds (abi : Material) (role : Role) (principal : Option DefinitionId)
    (autoBounds : Array DefinitionId) : Except String Bool := do
  objectBounds abi (← declaration abi role) principal autoBounds

private def dynamic (world : World) (abi : Material) (source : AutoDeclaration)
    (predicates : Array Nat) : Except String Bool := do
  let mut principal : Option DefinitionId := none
  let mut autoBounds := #[]
  for id in predicates do
    let some row := world.canonical.predicates[id]? | throw "object predicate identity absent"
    let some raw := world.canonical.definitions[row.definitionId]? | throw "object predicate definition absent"
    match row.kind with
    | .autoTrait => autoBounds := autoBounds.push raw
    | .trait =>
      unless principal.isNone do throw "object principal duplicated"
      principal := some raw
    | .projection => pure ()
  objectBounds abi source principal autoBounds

def check (world : World) (role : Role) (id : Nat) : Except String Bool :=
  go (world.canonical.types.size+1) #[] id
where
  go (fuel : Nat) (active : Array Nat) (id : Nat) : Except String Bool := do
    if ← trivial world id then return true
    let .succ fuel := fuel | throw "auto trait constituent traversal exhausted"
    unless !active.contains id do throw "auto trait cyclic constituent proof unsupported"
    let abi ← abiOfWorld world
    let source ← declaration abi role
    let node ← typeNode world id
    if let .dynamicTraitObject predicates .. := node.shape then
      return (← dynamic world abi source predicates)
    let (head,children) ← match node.shape with
      | .closure definition args count => do
        let some raw := world.canonical.definitions[definition]? | throw "auto trait closure identity absent"
        let some (.Type tuple) := args.back? | throw "auto trait closure upvar tuple absent"
        let .tuple fields := (← typeNode world tuple).shape | throw "auto trait closure upvars are not tuple"
        unless fields.size == count do throw "auto trait closure capture count mismatch"
        pure (AutoSelfHead.closure raw,#[tuple])
      | .tuple fields => pure (AutoSelfHead.tuple fields.size,fields)
      | .array child .. => pure (.rigid "array",#[child])
      | .slice child => pure (.rigid "slice",#[child])
      | _ => throw "auto trait nontrivial source type domain unsupported"
    exclude source head
    for child in children do
      unless (← go fuel (active.push id) child) do return false
    return true
end Miri.Input.SourceCompilerAutoTraits
