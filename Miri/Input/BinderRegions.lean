import Miri.Input.GenericSubstitution

/-! Region-only binder erasure/anonymization from pinned ty/fold.rs and
erase_regions.rs. Bound variables are reindexed by first occurrence, including
occurrences underneath nested binders; unused declarations are removed. This is
syntax normalization, not higher-ranked trait inference. -/
namespace Miri.Input.BinderRegions
open GenericSubstitution

def regionOnly (variables : Array BoundVariable) : Bool :=
  variables.all fun value => match value with | .region _ => true | _ => false

private def traverse (f : Term → StateT (Array Nat) (Except String) Term) :
    Terms → StateT (Array Nat) (Except String) Terms
  | .nil => pure .nil
  | .cons value rest => return .cons (← f value) (← traverse f rest)

private def anonymizeOwn (variables : Array BoundVariable) :
    Nat → Nat → Term → StateT (Array Nat) (Except String) Term
  | 0, _, _ => throw "binder anonymization traversal exhausted"
  | fuel + 1, depth, term => do
    match term with
    | .bound .region (.Bound index) variableIndex identity =>
      if index != depth then return term
      let some (.region expected) := variables[variableIndex]?
        | throw "bound region has no matching declared variable"
      unless identity == expected do throw "bound region identity contradicts its binder"
      let seen ← get
      let index ← match seen.findIdx? (· == variableIndex) with
        | some index => pure index
        | none => do set (seen.push variableIndex); pure seen.size
      pure (.bound .region (.Bound depth) index .anonymous)
    | .binder inner body => return .binder inner (← anonymizeOwn variables fuel (depth + 1) body)
    | .node sort tag payload terms =>
      return .node sort tag payload (← traverse (anonymizeOwn variables fuel depth) terms)
    | .definition sort tag identity terms =>
      return .definition sort tag identity (← traverse (anonymizeOwn variables fuel depth) terms)
    | _ => pure term

private def erase (preservePlaceholders : Bool) : Nat → Term → Except String Term
  | 0, _ => throw "binder region-erasure traversal exhausted"
  | fuel + 1, term => do
    match term with
    | .binder variables body =>
      unless regionOnly variables do throw "type/constant binder normalization is not implemented"
      let (body,seen) ← (anonymizeOwn variables (fuel + 1) 0 body).run #[]
      pure (.binder (seen.map fun _ => .region .anonymous) (← erase preservePlaceholders fuel body))
    | .bound .region .. => pure term
    | .placeholder .. =>
      if preservePlaceholders then pure term
      else if term.sort == .region then pure (.atom .region "erased" "")
      else pure term
    | _ =>
      if term.sort == .region then return .atom .region "erased" ""
      match term with
      | .node sort tag payload values => return .node sort tag payload (← values.mapM (erase preservePlaceholders fuel))
      | .definition sort tag identity values =>
        return .definition sort tag identity (← values.mapM (erase preservePlaceholders fuel))
      | _ => pure term

/-- Bound variables must be owned by an actual enclosing region binder.
All other unresolved variables remain explicit errors. -/
private def validateWith (preservePlaceholders : Bool) (scopes : Array (Array BoundVariable)) : Nat → Term → Except String Unit
  | 0, _ => throw "binder closed-type validation exhausted"
  | fuel + 1, term => do
    match term with
    | .bound .region (.Bound depth) variableIndex identity =>
      unless depth < scopes.size do throw "type retains an escaping bound region"
      let some scope := scopes[scopes.size - 1 - depth]? | throw "bound-region owner is absent"
      let some (.region expected) := scope[variableIndex]? | throw "bound-region variable is absent"
      unless identity == expected do throw "bound-region variable identity mismatch"
    | .placeholder .. =>
      unless preservePlaceholders do throw "normalized binder retains an unresolved placeholder"
    | .bound .. | .parameter .. | .inference .. =>
      throw "normalized binder retains unsupported or unresolved variables"
    | .binder variables body =>
      unless regionOnly variables do throw "normalized binder contains a type/constant variable"
      validateWith preservePlaceholders (scopes.push variables) fuel body
    | .node _ _ _ values | .definition _ _ _ values =>
      let _ ← values.mapM fun child => do validateWith preservePlaceholders scopes fuel child; pure child
      pure ()
    | .atom .. => pure ()

/-- Ordinary material normalization never retains solver placeholders. -/
def validateClosed (scopes : Array (Array BoundVariable)) (fuel : Nat) (term : Term) :
    Except String Unit := validateWith false scopes fuel term

/-- Alias-free types need no obligations or inference under a binder. Alias
normalization with bound obligations remains the trait solver's separate job. -/
def requireAliasFree : Nat → Term → Except String Unit
  | 0, _ => throw "binder alias-domain traversal exhausted"
  | fuel + 1, term => do
    match term with
    | .definition _ tag _ values =>
      if tag.startsWith "alias_" then
        throw "binder alias normalization requires its higher-ranked obligation provider"
      let _ ← values.mapM fun child => do requireAliasFree fuel child; pure child
      pure ()
    | .binder _ body => requireAliasFree fuel body
    | .node _ _ _ values =>
      let _ ← values.mapM fun child => do requireAliasFree fuel child; pure child
      pure ()
    | _ => pure ()

def eraseAndAnonymize (fuel : Nat) (term : Term) : Except String Term := do
  let result ← erase false fuel term
  validateClosed #[] fuel result
  pure result

/-- Region-only binder normalization inside a quantified query. Placeholders
of every sort remain symbolic. Syntax validation and actual universe ownership
must be checked by the caller; inference variables are still rejected. -/
def eraseAndAnonymizeScoped (fuel : Nat) (term : Term) : Except String Term := do
  let result ← erase true fuel term
  validateWith true #[] fuel result
  pure result

/-- TypeId hashing accepts open compiler subterms. Local binders validate and
anonymize their owned regions; escaping regions retain their raw identities.
This operation does not establish closedness for normalization or solver use. -/
def eraseAndAnonymizeOpen (fuel : Nat) (term : Term) : Except String Term := erase false fuel term

end Miri.Input.BinderRegions
