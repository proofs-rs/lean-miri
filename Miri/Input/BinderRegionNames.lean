import Miri.Input.GenericSubstitution

/-! Pinned pretty.rs RegionFolder/name_all_regions for region binders. The
first-occurrence order is significant and outer references crossing nested
binders do not enter the nested binder's `for<...>` list. -/
namespace Miri.Input.BinderRegionNames
open GenericSubstitution

private def sourceName (lookup : DefinitionIdentity → Except String String) :
    BoundIdentity → Except String (Option String)
  | .anonymous | .closureEnvironment => pure none
  | .namedForPrinting name => pure (some name)
  | .named identity => some <$> lookup identity

private def termList : Terms → List Term
  | .nil => [] | .cons child rest => child :: termList rest

def collect (lookup : DefinitionIdentity → Except String String) :
    Nat → Term → Except String (Array String)
  | 0, _ => throw "binder region-name collection exhausted"
  | fuel + 1, term => do
    match term with
    | .bound .region _ _ identity => pure (← sourceName lookup identity).toArray
    | .binder _ body => collect lookup fuel body
    | .node _ _ _ values | .definition _ _ _ values =>
      (termList values).foldlM (fun result child => do
        pure (result ++ (← collect lookup fuel child))) #[]
    | _ => pure #[]

private structure State where
  seen : Array (Nat × BoundIdentity × String) := #[]
  available : Array String
  nextIndex : Nat
  availableCount : Nat
  used : Array String
private abbrev M := StateT State (Except String)

private def lift (value : Except String α) : M α :=
  match value with | .ok result => pure result | .error error => throw error

private def nextName : M String := do
  let state ← get
  if let some name := state.available[0]? then
    set {state with
      available := state.available.extract 1 state.available.size
      nextIndex := state.nextIndex + 1}
    pure name
  else
    let mut index := state.nextIndex
    let mut name := "'z" ++ toString (index - state.availableCount)
    while state.used.contains name do
      index := index + 1
      name := "'z" ++ toString (index - state.availableCount)
    set {state with nextIndex := index + 1}
    pure name

private def traverse (f : Term → M Term) : Terms → M Terms
  | .nil => pure .nil
  | .cons value rest => return .cons (← f value) (← traverse f rest)

private def walk (lookup : DefinitionIdentity → Except String String)
    (variables : Array BoundVariable) : Nat → Nat → Term → M Term
  | 0, _, _ => throw "binder region naming traversal exhausted"
  | fuel + 1, depth, term => do
    match term with
    | .bound .region (.Bound index) variableIndex identity =>
      if index != depth then return term
      let some (.region expected) := variables[variableIndex]?
        | throw "printed bound region lacks its declared variable"
      unless expected == identity do throw "printed bound region contradicts its binder"
      let state ← get
      let name ← match state.seen.find? (fun entry => entry.1 == variableIndex && entry.2.1 == identity) with
        | some entry => pure entry.2.2
        | none => do
          let name ← match ← lift (sourceName lookup identity) with
            | some name => pure name | none => nextName
          modify fun state => {state with seen := state.seen.push (variableIndex,identity,name)}
          pure name
      pure (.bound .region (.Bound index) variableIndex (.namedForPrinting name))
    | .binder nested body => return .binder nested (← walk lookup variables fuel (depth + 1) body)
    | .node sort tag payload values =>
      return .node sort tag payload (← traverse (walk lookup variables fuel depth) values)
    | .definition sort tag identity values =>
      return .definition sort tag identity (← traverse (walk lookup variables fuel depth) values)
    | _ => pure term

structure Result where
  body : Term
  leadingText : String
  nextIndex : Nat

def name (lookup : DefinitionIdentity → Except String String) (fuel regionIndex : Nat)
    (used : Array String) (signature : Term) : Except String Result := do
  let .binder variables body := signature | throw "region naming requires the source binder"
  unless variables.all (fun value => match value with | .region _ => true | _ => false) do
    throw "type/constant binder diagnostic names are not implemented"
  let available := (Array.range 26).map (fun index => "'" ++ String.singleton (Char.ofNat (97 + index)))
    |>.filter (!used.contains ·)
  let (body,state) ← (walk lookup variables fuel 0 body).run
    {available,nextIndex := regionIndex,availableCount := available.size,used}
  let names := state.seen.map (·.2.2)
  let leadingText := if names.isEmpty then "" else "for<" ++ String.intercalate ", " names.toList ++ "> "
  pure ⟨body,leadingText,state.nextIndex⟩

end Miri.Input.BinderRegionNames
