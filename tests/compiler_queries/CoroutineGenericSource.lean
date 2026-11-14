import Miri.Input.CoroutineSourceInstantiation

open Miri.Input Miri.Input.GenericSubstitution
private def unit : Term := .node .type "tuple" "" .nil
private def owner : DefinitionIdentity := ⟨0,17⟩
private def moved : DefinitionIdentity := ⟨0,18⟩
private def source (kind : Term := unit) : CoroutineGenericSource := {
  owner, physicalOwner := owner, typeckOwner := ⟨0,16⟩, parentCount := 0,
  parameters := Array.replicate 5 .type, witnessParameters := #[],
  typeExpression := .definition .type "coroutine" owner (Terms.ofArray #[kind,unit,unit,unit,unit]),
  identityKind := kind, byMoveOwner := none,
  layout := {fields := #[], variants := #[#[],#[],#[]], variantSources := Array.replicate 3 ⟨0,0⟩, storageConflicts := #[]} }
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def reject (rows : Array CoroutineGenericSource) : IO Unit := do
  unless (CoroutineGenericSource.validateCatalog rows).toOption.isNone do
    throw (IO.userError "malformed coroutine generic source accepted")

def main : IO Unit := do
  let base := source
  let _ ← must (CoroutineGenericSource.validateCatalog #[base])
  let _ ← must (CoroutineSourceInstantiation.instantiate #[base] 100 base.typeExpression)
  reject #[base,base]
  reject #[{base with physicalOwner := moved}]
  reject #[{base with parameters := #[]}]
  reject #[{base with witnessParameters := #[.type]}]
  reject #[{base with identityKind := .atom .type "int" "i64"}]
  reject #[{base with typeExpression := .definition .type "coroutine" moved (Terms.ofArray (Array.replicate 5 unit))}]
  reject #[{base with byMoveOwner := some owner}]
  reject #[{base with layout := {base.layout with variants := #[]}}]
  reject #[{base with layout := {base.layout with storageConflicts := #[#[]]}}]
  reject #[{base with layout := {base.layout with variants := #[#[0],#[],#[]]}}]
  let borrowed := {source (.atom .type "int" "i16") with byMoveOwner := some moved}
  reject #[borrowed]
  let generated := {borrowed with physicalOwner := moved}
  let _ ← must (CoroutineGenericSource.validateCatalog #[borrowed,generated])
  reject #[borrowed,{generated with typeckOwner := moved}]
  let closed := .definition .type "coroutine" owner
    (Terms.ofArray #[.atom .type "int" "i32",unit,unit,unit,unit])
  let actual ← must (CoroutineSourceInstantiation.instantiate #[borrowed,generated] 100 closed)
  unless actual.source.physicalOwner == moved do throw (IO.userError "wrong generated physical owner")
  unless (CoroutineSourceInstantiation.instantiate #[base] 0 base.typeExpression).toOption.isNone do
    throw (IO.userError "exhausted source instantiation accepted")
  let forged := .definition .type "coroutine" owner
    (Terms.ofArray #[unit,.atom .type "bool" "",unit,unit,unit])
  unless (CoroutineSourceInstantiation.instantiate #[base] 100 forged).toOption.isNone do
    throw (IO.userError "forged synthetic resume source accepted")
  let field := {base with layout := {base.layout with
    fields := #[{
      typeId := .atom .type "bool" "", sourceInfo := ⟨0,0⟩,
      ignoreForTraits := false, debuginfoName := none}],
    variants := #[#[],#[],#[0]], storageConflicts := #[#[0]]}}
  let projected ← must (CoroutineSourceInstantiation.instantiate #[field] 100 field.typeExpression)
  unless (← must (projected.stateField 2 0)) == .atom .type "bool" "" do
    throw (IO.userError "state field did not preserve unwrapped saved type")
  for result in [projected.stateField 3 0, projected.stateField 2 1, projected.upvarField 0] do
    unless result.toOption.isNone do throw (IO.userError "invalid coroutine projection accepted")
  IO.println "PASS raw coroutine source controls and exact generated-owner substitution"
