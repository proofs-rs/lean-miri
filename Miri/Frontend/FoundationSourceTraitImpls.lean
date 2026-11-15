import Miri.Frontend.FoundationSourceAbi
import Miri.Frontend.FoundationGenericEnvironment
import Miri.Input.Model.SourceTraitImpls
namespace Miri.Frontend.Foundation.SourceTraitImplsParser
open Lean Miri.Input
private def raw (d : Document) (id : Nat) : Except String DefinitionId := do
  let some row := d.definitions[id]? | throw "trait impl source definition absent"
  unless (← row.getObjValAs? Nat "definition_id") == id do throw "trait impl definition identity mismatch"
  return ⟨← row.getObjValAs? Nat "crate_index",← row.getObjValAs? Nat "index"⟩
private def head (fuel : Nat) (j : Json) : Except String SourceAbi.AutoSelfHead := do
  let .succ fuel := fuel | throw "trait impl head nesting exhausted"
  let rawId (j : Json) : Except String DefinitionId := do
    return ⟨← j.getObjValAs? Nat "crate_index",← j.getObjValAs? Nat "index"⟩
  match ← j.getObjValAs? String "kind" with
  | "pattern" => return .pattern (← head fuel (← j.getObjVal? "base")) (← j.getObjValAs? String "pattern_kind")
  | "adt" => return .adt (← rawId (← j.getObjVal? "definition"))
  | "fn_def" => return .functionDefinition (← rawId (← j.getObjVal? "definition"))
  | "closure" => return .closure (← rawId (← j.getObjVal? "definition"))
  | "coroutine_closure" => return .coroutineClosure (← rawId (← j.getObjVal? "definition"))
  | "tuple" => return .tuple (← j.getObjValAs? Nat "arity")
  | "unknown" => return .unknown
  | tag =>
    unless #["fn_pointer","raw_pointer","reference","array","slice","str","bool","char","int","uint","float","never","dynamic"].contains tag do
      throw "trait impl rigid head unsupported"
    return .rigid tag
private def environment (d : Document) (j : Json) : Except String (Array SourceSymbols.ParameterKind × Array SourceAbi.Clause) := do
  let flat ← flattenEnvironment d j
  let parameters ← (← flat.getObjValAs? (Array Json) "parameters").mapM fun parameter => do
    match ← parameter.getObjValAs? String "kind" with
    | "type" => pure SourceSymbols.ParameterKind.typeParameter
    | "region" => pure .region
    | "const" => pure .constParameter
    | _ => throw "trait impl parameter kind unsupported"
  let clauses ← (← flat.getObjValAs? (Array Json) "clauses").mapM fun clause => do
    return (← SourceAbiParser.declaration d clause).1
  return (parameters,clauses)
private def scopedType (physical : SourceTypes.Material) (parameters : Array SourceSymbols.ParameterKind)
    (id : Nat) : Except String Unit := visit (physical.types.size+1) #[] id
where
  visit (fuel : Nat) (seen : Array Nat) (id : Nat) : Except String Unit := do
    let .succ fuel := fuel | throw "trait impl source type traversal exhausted"
    if seen.contains id then return
    let some row := physical.types[id]? | throw "trait impl source type reference absent"
    let child := visit fuel (seen.push id)
    match row with
    | .parameter index _ =>
      unless parameters[index]? == some .typeParameter do throw "trait impl type parameter slot mismatch"
    | .reference pointee _ region =>
      if let .earlyParameter index := region then
        unless parameters[index]? == some .region do throw "trait impl lifetime parameter slot mismatch"
      child pointee
    | .rawPointer pointee _ | .patternNotNull pointee => child pointee
    | .tuple fields => for field in fields do child field
    | .array element _ => child element
    | _ => pure ()
private def scopedClauses (physical : SourceTypes.Material) (parameters : Array SourceSymbols.ParameterKind)
    (clauses : Array SourceAbi.Clause) : Except String Unit := do
  for clause in clauses do
    match clause with
    | .trait _ _ arguments => for argument in arguments do scopedType physical parameters argument
    | .projection _ _ arguments term =>
      for argument in arguments do scopedType physical parameters argument
      scopedType physical parameters term
    | .typeOutlives type _ => scopedType physical parameters type
    | .regionOutlives longer shorter =>
      for region in #[longer,shorter] do
        if let .earlyParameter index := region then
          unless parameters[index]? == some .region do throw "trait impl region parameter slot mismatch"
    | .constHasType index type =>
      unless parameters[index]? == some .constParameter do throw "trait impl const parameter slot mismatch"
      scopedType physical parameters type
    | .unsupported _ => pure ()
def material (d : Document) (physical : SourceTypes.Material) : Except String (Option SourceTraitImpls.Material) := do
  let source ← match d.source.getObjVal? "trait_impl_source" with
    | .error _ | .ok .null => return none
    | .ok source => pure source
  let mut declarations : Array SourceTraitImpls.Declaration := #[]
  for row in (← source.getObjValAs? (Array Json) "declarations") do
    let definition ← raw d (← row.getObjValAs? Nat "definition")
    unless !(declarations.any (·.definition == definition)) do throw "trait impl declaration duplicated"
    let (parameters,clauses) ← environment d (← row.getObjVal? "environment")
    let hasSelf ← row.getObjValAs? Bool "has_self"
    let mut superClauses := #[]
    for clause in clauses do
      let reflexive ← match clause with
        | .trait traitDefinition none arguments =>
          if traitDefinition == definition then do
            let [self] := arguments.toList | throw "trait declaration Self assumption arity invalid"
            unless hasSelf && parameters[0]? == some .typeParameter do throw "trait declaration Self slot absent"
            let some (.parameter 0 _) := physical.types[self]? | throw "trait declaration Self assumption identity invalid"
            pure true
          else pure false
        | _ => pure false
      if !reflexive then superClauses := superClauses.push clause
    scopedClauses physical parameters superClauses
    let mut implementations : Array SourceTraitImpls.Implementation := #[]
    for item in (← row.getObjValAs? (Array Json) "implementations") do
      let id ← raw d (← item.getObjValAs? Nat "definition")
      unless !(implementations.any (·.definition == id)) do throw "trait impl header duplicated"
      let source ← item.getObjVal? "syntax"
      let header ← if source == .null then pure none else do
        let (parameters,clauses) ← environment d (← source.getObjVal? "environment")
        let arguments ← (← source.getObjValAs? (Array Json) "trait_arguments").mapM fun argument => do
          unless (← argument.getObjValAs? String "kind") == "type" do throw "trait impl non-type trait argument unsupported"
          argument.getObjValAs? Nat "type"
        let selfType ← source.getObjValAs? Nat "self_type"
        unless arguments[0]? == some selfType do throw "trait impl Self argument identity mismatch"
        for argument in arguments do scopedType physical parameters argument
        scopedClauses physical parameters clauses
        let nonConst ← match ← source.getObjValAs? String "constness" with
          | "NotConst" => pure true
          | "Const" => pure false
          | _ => throw "trait impl constness unsupported"
        pure (some (SourceTraitImpls.Syntax.mk parameters selfType arguments clauses
          nonConst (← source.getObjValAs? Bool "final")))
      let polarity ← match ← item.getObjValAs? String "polarity" with
        | "Positive" => pure SourceTraitImpls.Polarity.positive
        | "Negative" => pure .negative
        | _ => throw "trait impl polarity unsupported"
      implementations := implementations.push ⟨id,← head 256 (← item.getObjVal? "outer_head"),polarity,header⟩
    declarations := declarations.push ⟨definition,← row.getObjValAs? Bool "is_auto",hasSelf,parameters,
      ← row.getObjValAs? Nat "associated_item_count",superClauses,implementations⟩
  return some ⟨declarations⟩
end Miri.Frontend.Foundation.SourceTraitImplsParser
