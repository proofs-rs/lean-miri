import Miri.Input.GenericInstantiation

open Miri.Input Miri.Input.GenericSubstitution Miri.Input.GenericInstantiation

private def adt : AdtShape := {
  definition := 0, kind := .structKind, args := #[.Type 1], variants := #[],
  representation := {
    integer := none, alignBytes := none, packBytes := none,
    flagsBits := 0, scalableElement := none, fieldShuffleSeed := 0 } }

private def sourceTemplate : DefinitionTemplate := {
  parameters := #[.type],
  typeExpression := .definition .type "adt" ⟨3, 9⟩ (.cons (.parameter .type 0) .nil),
  signatureExpression := none,
  fields := #[⟨0, 0, .parameter .type 0⟩] }

private def context : Context := {
  types := #[
    {id := 0, display := "same", layoutId := 0, shape := .uint (.known .u8)},
    {id := 1, display := "same", layoutId := 0, shape := .uint (.known .u32)},
    {id := 2, display := "same", layoutId := 0, shape := .str},
    {id := 3, display := "same", layoutId := 0, shape := .tuple #[0, 1]},
    {id := 4, display := "same", layoutId := 0, shape := .adt adt}],
  definitions := #[{crateIndex := 3, index := 9, genericTemplate := some sourceTemplate}],
  constants := #[], pointerBytes := 8 }

private def rejected (result : Except String α) : Bool :=
  match result with | .error _ => true | .ok _ => false

def main : IO Unit := do
  let checked : Except String Unit := do
    let context ← if dense : TypeArena.isDense context.types = true then
      pure {context with denseTypes := some ⟨dense⟩}
      else throw "test type universe is not dense"
    let field ← instantiateFieldType context 64 0 #[.Type 1] 0 0
    unless (← resolveType context 64 field) == 1 do throw "raw field substitution picked wrong identity"
    let raw ← ofType context 64 4
    unless (← resolveType context 64 raw) == 4 do throw "ADT definition identity roundtrip failed"
    let pointer := Term.node .type "raw_pointer" "mutable" (.cons field .nil)
    let id ← resolveType context 64 pointer
    unless id ≥ context.types.size do throw "novel pointer did not receive a new identity"
    unless (← ofType context 64 id) == pointer do throw "novel pointer shape roundtrip failed"
    unless rejected (resolveType context 64 (.node .type "raw_pointer" "immutable" (.cons field .nil))) do
      throw "unsupported immutable constructor was accepted"
    unless rejected (resolveType context 64 (.definition .type "adt" ⟨3, 10⟩ (.cons field .nil))) do
      throw "unrelated ADT with equal display/layout was accepted"
    let duplicate : TypeNode := {id := context.types.size, display := "same", layoutId := 0, shape := .uint (.known .u32)}
    let ambiguous := {context with types := context.types.push duplicate, denseTypes := none}
    match resolveType ambiguous 64 field with
    | .error "ambiguous canonical generic type identity" => pure ()
    | _ => throw "duplicate semantic candidates did not retain ambiguity rejection"
    unless rejected (instantiateFieldType context 64 0 #[] 0 0) do
      throw "missing generic arguments were accepted"
  match checked with
  | .ok () => IO.println "generic declaration field/identity/lazy-constructor checks passed"
  | .error error => throw (IO.userError error)
