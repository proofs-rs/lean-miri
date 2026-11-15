import Miri.Input.Model.SourceTraitImpls
import Miri.Input.SourceTypeQueries

namespace Miri.Input.SourceTraitSelection
open SourceTypes SourceAbi

private def raw (physical : SourceTypes.Material) (id : Nat) : Except String DefinitionId := do
  let some definition := physical.definitions[id]? | throw "trait source definition absent"
  return definition.raw

private def head (physical : SourceTypes.Material) : Concrete → Except String AutoSelfHead
  | .primitive kind _ => pure (.rigid kind)
  | .tuple fields => pure (.tuple fields.size)
  | .array .. => pure (.rigid "array")
  | .pointer kind _ => pure (.rigid (if kind.startsWith "reference_" then "reference" else "raw_pointer"))
  | .functionPointer .. => pure (.rigid "fn_pointer")
  | .dynamicObject .. => pure (.rigid "dynamic")
  | .nominal definition _ => AutoSelfHead.adt <$> raw physical definition
  | .closure definition _ => AutoSelfHead.closure <$> raw physical definition
  | .patternNotNull base => head physical base
  | .patternRange .. => throw "Unsupported range-pattern trait head"

private def disjoint : AutoSelfHead → AutoSelfHead → Bool
  | .pattern base _, goal => disjoint base goal
  | .unknown,_ => false
  | .adt a,.adt b | .closure a,.closure b | .functionDefinition a,.functionDefinition b |
      .coroutineClosure a,.coroutineClosure b => a != b
  | .tuple a,.tuple b => a != b
  | .rigid a,.rigid b => a != b
  | _,_ => true

/-- First-order type matching binds source generic slots; unsupported details
cannot certify that a potentially relevant implementation is disjoint. -/
private def matchType (physical : SourceTypes.Material) (parameters : Array SourceSymbols.ParameterKind)
    (pattern : Nat) (goal : Concrete) (bindings : Array (Option Concrete)) : Except String (Option (Array (Option Concrete))) :=
  go 1024 pattern goal bindings
where
  go (fuel : Nat) (pattern : Nat) (goal : Concrete) (bindings : Array (Option Concrete)) : Except String (Option (Array (Option Concrete))) := do
    let .succ fuel := fuel | throw "trait impl pattern recursion exhausted"
    let some expr := physical.types[pattern]? | throw "trait impl source type absent"
    match expr,goal with
    | .parameter index _,_ =>
      unless parameters[index]? == some .typeParameter do throw "trait impl type parameter slot invalid"
      if bindings[index]?.join |>.isSome then
        throw "trait impl repeated parameter equality unsupported"
      return some (bindings.setIfInBounds index (some goal))
    | .primitive kind name,.primitive actual actualName =>
      return if kind == actual && name == actualName then some bindings else none
    | .rawPointer child mutability,.pointer kind pointee =>
      if kind != (if mutability == .Mut then "raw_pointer_mut" else "raw_pointer_const") then return none
      go fuel child pointee bindings
    | .reference child mutability _,.pointer kind pointee =>
      if kind != s!"reference_erased_{if mutability == .Mut then "mut" else "const"}" &&
          kind != s!"reference_static_{if mutability == .Mut then "mut" else "const"}" then return none
      go fuel child pointee bindings
    | .tuple patterns,.tuple goals =>
      if patterns.size != goals.size then return none
      let mut current := bindings
      for (pattern,goal) in patterns.zip goals do
        let some next ← go fuel pattern goal current | return none
        current := next
      return some current
    | .patternNotNull child,.patternNotNull base => go fuel child base bindings
    | .unsupported _,_ | .projectionAlias ..,_ | .patternRange ..,_ => throw "trait impl type pattern unsupported"
    | .nominal ..,_ | .functionPointer ..,_ | .closure ..,_ | .dynamicObject ..,_ | .array ..,_ |
        .functionDefinition ..,_ => throw "trait impl nontrivial type pattern unsupported"
    | _,_ => return none

/-- Complete finite manual headers precede auto structural candidates. The
pinned selector suppresses an auto candidate whenever a relevant manual impl
exists, even if its where clauses fail. -/
def check (physical : SourceTypes.Material) (abi : SourceAbi.Material)
    (material : SourceTraitImpls.Material)
    (builtin : BuiltinTrait → Concrete → Except String Bool)
    (definition : DefinitionId) (type : Concrete) : Except String Bool := go 1024 definition type
where
  go (fuel : Nat) (definition : DefinitionId) (type : Concrete) : Except String Bool := do
    let .succ fuel := fuel | throw "trait obligation recursion unsupported"
    let [declaration] := (material.declarations.filter (·.definition == definition)).toList
      | throw "trait complete source declaration absent/ambiguous"
    unless declaration.hasSelf && declaration.parameters == #[.typeParameter] && declaration.associatedItems == 0 do
      throw "trait declaration generic/associated-item domain unsupported"
    let goalHead ← head physical type
    let mut relevant := false
    let mut selected : Option Bool := none
    for implementation in declaration.implementations do
      unless disjoint implementation.outerHead goalHead do
        relevant := true
        let some details := implementation.header | throw "trait relevant impl details unavailable"
        unless details.nonConst && details.isFinal && details.traitArguments.size == 1 do
          throw "trait conditional specialization/const header unsupported"
        let some bindings ← matchType physical details.parameters details.selfType type
            (Array.replicate details.parameters.size none) | continue
        if ← clauses fuel bindings details.clauses then
          unless selected.isNone do throw "trait applicable manual implementations ambiguous"
          let value ← match implementation.polarity with
            | .positive => pure true
            | .negative => pure false
            | .reservation => throw "trait reservation impl unsupported"
          selected := some value
    if let some value := selected then return value
    if relevant then throw "trait relevant manual candidate could not be resolved"
    unless declaration.isAuto do throw "ordinary trait has no matching supported manual impl"
    unless (← clauses fuel #[some type] declaration.superClauses) do return false
    match type with
    | .dynamicObject object =>
      let mut bounds := #[]
      for bound in object.autoTraits do bounds := bounds.push (← raw physical bound)
      if bounds.contains definition then return true
      if let some principal := object.principal then
        objectParents abi definition (abi.objectTraits.size+1) #[] (← raw physical principal)
      return false
    | .primitive "str" _ => throw "trait str requires slice constituent source support"
    | .primitive .. | .functionPointer .. => return true
    | .tuple fields =>
      for field in fields do unless (← go fuel definition field) do return false
      return true
    | .closure _ arguments =>
      let some (.tuple fields) := arguments.back? | throw "trait closure upvar tuple absent"
      for field in fields do unless (← go fuel definition field) do return false
      return true
    | .array child _ | .pointer _ child | .patternNotNull child => go fuel definition child
    | _ => throw "trait auto constituents source domain unsupported"
  clauses (fuel : Nat) (bindings : Array (Option Concrete)) (rows : Array Clause) : Except String Bool := do
    for clause in rows do
      match clause with
      | .trait definition role arguments =>
        let [self] := arguments.toList | throw "trait impl where-clause arguments unsupported"
        let self ← SourceTypes.instantiate physical bindings #[] self
        let satisfied ← match role with
          | some role => builtin role self
          | none => go fuel definition self
        unless satisfied do return false
      | _ => throw "trait impl where-clause kind unsupported"
    return true
  objectParents (abi : SourceAbi.Material) (target : DefinitionId) (fuel : Nat)
      (active : Array DefinitionId) (definition : DefinitionId) : Except String Unit := do
    unless target != definition do throw "trait inherited object bound rebasing unsupported"
    unless !active.contains definition do throw "trait object supertrait cycle unsupported"
    let .succ fuel := fuel | throw "trait object supertrait recursion exhausted"
    let [row] := (abi.objectTraits.filter (·.definition == definition)).toList
      | throw "trait object supertrait declaration absent/ambiguous"
    unless row.unsupportedSuperClauses.isEmpty do throw "trait object super-clause unsupported"
    for parent in row.superTraits do objectParents abi target fuel (active.push definition) parent
end Miri.Input.SourceTraitSelection
