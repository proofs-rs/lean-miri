import Miri.Input.CoroutineGenericSource

/-! Substitution and exact physical-body selection from raw coroutine source.
No compiler layout answer or closed runtime type catalog is an input. -/
namespace Miri.Input.CoroutineSourceInstantiation
open GenericSubstitution

private def terms : Terms → Array Term
  | .nil => #[] | .cons head tail => #[head] ++ terms tail

structure Result where
  source : CoroutineGenericSource
  arguments : Array Term
  saved : Array Term
  upvars : Array Term
  witness : Term

/-- A complete closed coroutine constructor selects one declaration. Synthetic
resume/yield/return/upvar syntax must match source substitution; only kind may
change along the pinned by-move transition. -/
def instantiate (sources : Array CoroutineGenericSource) (fuel : Nat) (coroutine : Term) :
    Except String Result := do
  CoroutineGenericSource.validateCatalog sources
  GenericSyntax.validate {erasedRegions := true, lateRegions := true} fuel .type coroutine
  let .definition .type "coroutine" owner children := coroutine |
    throw "coroutine source instantiation: type is not a coroutine"
  let arguments := terms children
  let ordinary := sources.filter fun row => row.owner == owner && row.physicalOwner == owner
  let #[header] := ordinary | throw "coroutine source instantiation: ordinary owner missing or ambiguous"
  unless arguments.size == header.parameters.size do
    throw "coroutine source instantiation: argument domain mismatch"
  let some requestedTerm := arguments[header.parentCount]? |
    throw "coroutine source instantiation: kind argument missing"
  let identity ← CoroutineBodyDispatch.kindOfTerm header.identityKind
  let requested ← CoroutineBodyDispatch.kindOfTerm requestedTerm
  let physical ← CoroutineBodyDispatch.select ⟨owner,identity,header.byMoveOwner,.ordinary⟩ requested
  let selected := sources.filter fun row => row.owner == owner && row.physicalOwner == physical
  let #[source] := selected | throw "coroutine source instantiation: physical owner missing or ambiguous"
  let expected ← GenericSubstitution.instantiate fuel (arguments.take source.parentCount) source.typeExpression
  let .definition .type "coroutine" expectedOwner expectedChildren := expected |
    throw "coroutine source instantiation: substituted source constructor differs"
  let expectedArguments := terms expectedChildren
  unless expectedOwner == owner && expectedArguments.size == arguments.size do
    throw "coroutine source instantiation: substituted source owner/domain differs"
  for i in [:arguments.size] do
    unless i == source.parentCount do
      unless arguments[i]? == expectedArguments[i]? do
        throw "coroutine source instantiation: synthetic or parent source syntax differs"
  let saved ← source.layout.fields.mapM fun field =>
    GenericSubstitution.instantiate fuel arguments field.typeId
  let some upvars := arguments[source.parentCount + 4]? |
    throw "coroutine source instantiation: upvar argument absent"
  let .node .type "tuple" "" upvarChildren := upvars |
    throw "coroutine source instantiation: upvar argument is not a tuple"
  let witnessArguments := (arguments.take source.witnessParameters.size).map fun argument =>
    if argument.sort == .region then Term.atom .region "erased" "" else argument
  pure ⟨source,arguments,saved,terms upvarChildren,
    .definition .type "coroutine_witness" owner (Terms.ofArray witnessArguments)⟩

end Miri.Input.CoroutineSourceInstantiation
