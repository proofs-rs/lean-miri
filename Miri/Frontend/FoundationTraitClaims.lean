import Miri.Frontend.Foundation
import Miri.Frontend.FoundationTraitBuiltins

/-! A finite source-header matcher, not a general trait solver. The producer
captures every impl of a local ordinary methodless trait before any demand.
Positive primitive headers and canonical one-parameter fixed-array blankets
are supported. Negative, automatic and method-dispatch fallbacks are absent. -/
namespace Miri.Frontend.Foundation
open Lean

private def primitiveAllowed (kind name : String) : Bool :=
  (kind == "bool" || kind == "char") && name == "" ||
    kind == "int" && #["i8", "i16", "i32", "i64", "i128", "isize"].contains name ||
    kind == "uint" && #["u8", "u16", "u32", "u64", "u128", "usize"].contains name ||
    kind == "float" && #["f16", "f32", "f64", "f128"].contains name

/-- Decide one fully substituted local trait obligation from the
complete source headers. False means no supported source impl matches, whereas
missing or unsupported material returns an error. -/
def localTraitClaim (definition : Json) (self : ConcreteType) : Except String Bool := do
  let source ← definition.getObjVal? "local_trait"
  unless (← source.getObjValAs? String "source_kind") == "local_ordinary_methodless_trait" &&
      (← source.getObjValAs? Bool "complete_impl_headers") do
    throw "unsupported/incomplete local trait source"
  unless (← source.getObjValAs? (Array Json) "associated_items").isEmpty do
    throw "unsupported local trait declaration"
  -- MetaSized is the pinned compiler's implicit supertrait. The supported
  -- primitive Self domain has fixed metadata; no auto-trait fallback is used.
  for clause in (← source.getObjValAs? (Array Json) "super_clauses") do
    unless (← clause.getObjValAs? String "kind") == "self_trait" &&
        (← clause.getObjValAs? String "lang_item") == "meta_sized" &&
        (← clause.getObjValAs? Nat "self_parameter") == 0 do
      throw "unsupported local trait super clause"
  let parameters ← source.getObjValAs? (Array Json) "parameters"
  unless parameters.size == 1 do throw "unsupported local trait parameters"
  let some parameter := parameters[0]? | throw "missing local trait Self"
  unless (← parameter.getObjValAs? String "kind") == "self" &&
      (← parameter.getObjValAs? Nat "index") == 0 do throw "invalid local trait Self"
  let _ ← localImplCopy self -- validates the entire small Sized/MetaSized domain
  let mut matchCount := 0
  let mut identities : Array (Nat × Nat) := #[]
  for header in (← source.getObjValAs? (Array Json) "implementations") do
    unless (← header.getObjValAs? String "polarity") == "positive" do
      throw "unsupported local trait impl polarity"
    let identity := (← header.getObjValAs? Nat "crate_index", ← header.getObjValAs? Nat "index")
    unless !(identities.contains identity) do throw "duplicate local trait impl identity"
    identities := identities.push identity
    let parameters ← header.getObjValAs? (Array Json) "parameters"
    let clauses ← header.getObjValAs? (Array Json) "clauses"
    let implemented ← header.getObjVal? "self_type"
    let implKind ← implemented.getObjValAs? String "kind"
    let applies ← if parameters.isEmpty then do
      unless clauses.isEmpty do throw "unsupported conditional primitive impl"
      let implName ← implemented.getObjValAs? String "name"
      unless primitiveAllowed implKind implName do throw "unsupported local trait impl Self"
      match self with
      | .primitive kind name => pure (implKind == kind && implName == name)
      | _ => pure false
    else do
      unless parameters.size == 1 && implKind == "array_pattern" do
        throw "unsupported generic local impl pattern"
      let some parameter := parameters[0]? | throw "missing local impl parameter"
      unless (← parameter.getObjValAs? String "kind") == "type" &&
          (← parameter.getObjValAs? Nat "index") == 0 &&
          (← implemented.getObjValAs? Nat "element_parameter") == 0 do
        throw "noncanonical local impl parameter"
      let some length := (← implemented.getObjValAs? String "length").toNat?
        | throw "invalid local impl array length"
      let candidate ← match self with
        | .array element actual =>
          if actual == length then pure (some (← localImplCopy element)) else pure none
        | _ => pure none
      let mut satisfied := candidate.isSome
      for clause in clauses do
        unless (← clause.getObjValAs? String "kind") == "parameter_trait" &&
            (← clause.getObjValAs? Nat "parameter") == 0 do
          throw "unsupported local impl clause"
        match ← clause.getObjValAs? String "lang_item" with
        | "sized" | "meta_sized" =>
          unless (← clause.getObjValAs? String "implementation_source") == "compiler_builtin" do
            throw "unsupported local impl sizedness source"
          pure () -- validated structural domain above
        | "copy" =>
          unless (← clause.getObjValAs? String "implementation_source") == "pinned_core_marker" do
            throw "unsupported local impl Copy implementation source"
          satisfied := satisfied && candidate == some true
        | _ => throw "unsupported local impl builtin clause"
      pure satisfied
    if applies then matchCount := matchCount + 1
  unless matchCount ≤ 1 do throw "duplicate matching local trait impls"
  return matchCount == 1

end Miri.Frontend.Foundation
