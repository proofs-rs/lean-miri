import Lean

/-! Pure source Fn-family vtable candidate plans. The plan contains method-or-
vacancy obligations, not resolved Instances, vtable allocations, addresses or
compiler answers. Closure selection, impossible predicates, shims and physical
allocation identity remain necessary before executable vtable construction. -/
namespace Miri.Frontend.Foundation
open Lean

structure FnVtableDeclarations where
  definitions : Array Json
  roots : Array Json
  declarations : Array Json
  noTraitVptr : Bool

structure FnSourceSupertrait where
  definition : Nat
  arguments : Array Json

/-- Retain the complete finite source graph, rejecting duplicate identities. -/
def readFnVtableDeclarations (document : Json) : Except String FnVtableDeclarations := do
  let source ← document.getObjVal? "fn_vtable_source"
  if source == Json.null then throw "Fn vtable declaration source unavailable"
  let definitions ← document.getObjValAs? (Array Json) "definitions"
  let roots ← source.getObjValAs? (Array Json) "roots"
  let declarations ← source.getObjValAs? (Array Json) "declarations"
  let mut seen := #[]
  for row in declarations do
    let id ← row.getObjValAs? Nat "definition"
    unless id < definitions.size do throw "Fn source declaration definition out of bounds"
    if seen.contains id then throw "duplicate Fn source declaration"
    seen := seen.push id
  return ⟨definitions,roots,declarations,← source.getObjValAs? Bool "no_trait_vptr"⟩

def fnSourceDeclaration (source : FnVtableDeclarations) (definition : Nat) : Except String Json := do
  let rows ← source.declarations.filterM fun row => return (← row.getObjValAs? Nat "definition") == definition
  unless rows.size == 1 do throw "missing exact Fn source declaration"
  let some row := rows[0]? | throw "Fn declaration absent"
  unless (← row.getObjValAs? Bool "core_source") && (← row.getObjValAs? Bool "has_self") do
    throw "Fn declaration lacks pinned core Self source"
  return row

def fnSourceRoot (source : FnVtableDeclarations) (kind : String) : Except String Nat := do
  unless #["fn","fn_mut","fn_once"].contains kind do throw "unsupported Fn source root kind"
  let rows ← source.roots.filterM fun row => return (← row.getObjValAs? String "kind") == kind
  unless rows.size == 1 do throw "missing or duplicate Fn language root"
  let some row := rows[0]? | throw "Fn language root absent"
  let some id ← row.getObjValAs? (Option Nat) "definition" | throw "Fn language item source unavailable"
  let declaration ← fnSourceDeclaration source id
  unless (← declaration.getObjValAs? String "lang_item") == kind do throw "Fn root declaration kind mismatch"
  return id

def fnSourceSupertraits (source : FnVtableDeclarations) (definition : Nat) :
    Except String (Array FnSourceSupertrait) := do
  let declaration ← fnSourceDeclaration source definition
  let mut result := #[]
  for clause in (← declaration.getObjValAs? (Array Json) "super_clauses") do
    match ← clause.getObjValAs? String "kind" with
    | "non_trait" => let _ ← clause.getObjValAs? String "source"
    | "trait" =>
      unless (← clause.getObjValAs? String "polarity") == "Positive" &&
          (← clause.getObjValAs? (Array Json) "bound_variables").isEmpty do
        throw "bound or negative Fn source supertrait unsupported"
      let definition ← clause.getObjValAs? Nat "definition"
      let _ ← fnSourceDeclaration source definition
      result := result.push ⟨definition,← clause.getObjValAs? (Array Json) "arguments"⟩
    | _ => throw "unknown Fn source supertrait kind"
  return result

inductive FnVtableSlotCandidate where
  | dropInPlace | size | alignment
  | methodOrVacant (traitDefinition methodDefinition : Nat) (name : String)
  deriving Repr, DecidableEq

structure FnVtableCandidatePlan where
  principal : Nat
  slots : Array FnVtableSlotCandidate
  noTraitVptr : Bool
  deriving Repr, DecidableEq

private def param (index : Nat) : Json := Json.mkObj [("kind",toJson "param"),("index",toJson index)]
private def typeArgument (index : Nat) : Json := Json.mkObj [("kind",toJson "type"),("type",param index)]

private def checkParameters (row : Json) (count : Nat) : Except String Unit := do
  let parameters ← row.getObjValAs? (Array Json) "parameters"
  unless parameters.size == count do throw "Fn declaration parameter count mismatch"
  for h : i in [:parameters.size] do
    unless (← parameters[i].getObjValAs? Nat "index") == i &&
        (← parameters[i].getObjValAs? String "kind") == "type" &&
        !(← parameters[i].getObjValAs? Bool "has_default") do
      throw "noncanonical Fn declaration source parameter"

private def outputIdentity (source : FnVtableDeclarations) : Except String Nat := do
  let row ← fnSourceDeclaration source (← fnSourceRoot source "fn_once")
  let outputs ← (← row.getObjValAs? (Array Json) "associated_items").filterM fun item =>
    return (← item.getObjValAs? String "kind") == "type" && (← item.getObjValAs? String "name") == "Output"
  unless outputs.size == 1 do throw "FnOnce Output source identity absent or duplicate"
  let some output := outputs[0]? | throw "FnOnce Output absent"
  let id ← output.getObjValAs? Nat "definition"
  unless id < source.definitions.size do throw "FnOnce Output definition out of bounds"
  return id

private def methodCandidate (source : FnVtableDeclarations) (traitId : Nat) (kind : String)
    (item : Json) : Except String FnVtableSlotCandidate := do
  let expected := if kind == "fn_once" then "call_once" else if kind == "fn_mut" then "call_mut" else "call"
  unless (← item.getObjValAs? String "name") == expected do throw "unexpected Fn source method"
  let methodId ← item.getObjValAs? Nat "definition"
  unless methodId < source.definitions.size do throw "Fn method definition out of bounds"
  let method ← item.getObjVal? "method"
  unless (← method.getObjValAs? Bool "is_method") && !(← method.getObjValAs? Bool "final") &&
      !(← method.getObjValAs? Bool "variadic") && (← method.getObjValAs? String "abi") == "RustCall" &&
      (← method.getObjValAs? String "safety") == "Safe" && (← method.getObjValAs? Nat "parent_count") == 2 &&
      (← method.getObjValAs? (Array Json) "own_parameters").isEmpty &&
      (← method.getObjValAs? (Array Json) "own_clauses").isEmpty do
    throw "Fn method declaration lies outside supported virtual source shape"
  let inputs ← method.getObjValAs? (Array Json) "inputs"
  unless inputs.size == 2 && inputs[1]? == some (param 1) do throw "Fn method argument source mismatch"
  let some receiver := inputs[0]? | throw "Fn method receiver absent"
  let binders ← method.getObjValAs? (Array String) "bound_variables"
  if kind == "fn_once" then
    unless receiver == param 0 && binders.isEmpty do throw "FnOnce receiver source mismatch"
  else
    unless binders.size == 1 && binders.all (·.startsWith "Region(") &&
        (← receiver.getObjValAs? String "kind") == "reference" &&
        (← receiver.getObjValAs? Bool "mutable") == (kind == "fn_mut") &&
        (← receiver.getObjVal? "pointee") == param 0 do throw "Fn reference receiver source mismatch"
    let region ← receiver.getObjVal? "region"
    unless (← region.getObjValAs? String "kind") == "bound" &&
        (← region.getObjValAs? Nat "binder") == 0 && (← region.getObjValAs? Nat "variable") == 0 do
      throw "Fn receiver region binder source mismatch"
    let _ ← region.getObjValAs? String "source_kind"
  let output ← method.getObjVal? "output"
  unless (← output.getObjValAs? String "kind") == "projection" &&
      (← output.getObjValAs? Nat "definition") == (← outputIdentity source) &&
      (← output.getObjValAs? (Array Json) "arguments") == #[typeArgument 0,typeArgument 1] &&
      #["Yes","No"].contains (← output.getObjValAs? String "rigid") do
    throw "Fn source output projection mismatch"
  return .methodOrVacant traitId methodId expected

/-- Compute source slot positions for the pinned linear Fn family. A slot is
explicitly method-or-vacant: no impossible-clause check or Instance resolver is
assumed, and no physical vtable can be obtained from this plan alone. -/
def fnVtableCandidates (source : FnVtableDeclarations) (principal : Nat) : Except String FnVtableCandidatePlan := do
  let roots ← #["fn","fn_mut","fn_once"].mapM (fnSourceRoot source)
  unless roots.contains principal do throw "vtable source principal is outside Fn family"
  let (_, methods) ← visit (source.declarations.size + 1) #[] #[] principal
  return ⟨principal, #[.dropInPlace,.size,.alignment] ++ methods,source.noTraitVptr⟩
where
  visit (fuel : Nat) (active seen : Array Nat) (id : Nat) :
      Except String (Array Nat × Array FnVtableSlotCandidate) := do
    if active.contains id then throw "cyclic Fn supertrait source"
    if seen.contains id then return (seen,#[])
    let .succ fuel := fuel | throw "Fn source traversal exhausted"
    let row ← fnSourceDeclaration source id
    let kind ← row.getObjValAs? String "lang_item"
    let marker := kind == "meta_sized" || kind == "pointee_sized"
    unless marker || #["fn","fn_mut","fn_once"].contains kind do throw "unsupported Fn source supertrait declaration"
    checkParameters row (if marker then 1 else 2)
    let mut seen := seen.push id
    let mut methods := #[]
    let mut methodSuperCount := 0
    for supertrait in (← fnSourceSupertraits source id) do
      let target ← fnSourceDeclaration source supertrait.definition
      let targetKind ← target.getObjValAs? String "lang_item"
      let targetMarker := targetKind == "meta_sized" || targetKind == "pointee_sized"
      unless supertrait.arguments == (if targetMarker then #[typeArgument 0] else #[typeArgument 0,typeArgument 1]) do
        throw "Fn supertrait source argument rebase unsupported"
      unless targetMarker do
        methodSuperCount := methodSuperCount + 1
        unless (kind == "fn" && targetKind == "fn_mut") ||
            (kind == "fn_mut" && targetKind == "fn_once") do throw "Fn family inheritance source mismatch"
      let (next, inherited) ← visit fuel (active.push id) seen supertrait.definition
      seen := next
      methods := methods ++ inherited
    unless methodSuperCount == (if kind == "fn" || kind == "fn_mut" then 1 else 0) do
      throw "Fn source method-supertrait completeness mismatch"
    let items ← row.getObjValAs? (Array Json) "associated_items"
    let mut ownCount := 0
    for item in items do
      match ← item.getObjValAs? String "kind" with
      | "method" =>
        if marker then throw "Fn marker source unexpectedly has a method"
        methods := methods.push (← methodCandidate source id kind item)
        ownCount := ownCount + 1
      | "type" =>
        unless kind == "fn_once" && (← item.getObjValAs? String "name") == "Output" do
          throw "unsupported Fn source associated type"
      | _ => throw "unsupported Fn source associated item"
    unless ownCount == (if marker then 0 else 1) do throw "Fn source method completeness mismatch"
    return (seen,methods)

end Miri.Frontend.Foundation
