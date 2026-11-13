import Miri.Input.WorldDynamicData
import Miri.Input.WorldVTableInstance

/-! Direct-principal ground ObjectCandidate slice. No inference, upcast or
projection obligation is silently discharged. Pinned candidate_assembly.rs:916,
confirmation.rs:431 and rustc_ty_utils/src/instance.rs:246. -/
namespace Miri.Input.WorldObjectCandidate
open GenericSubstitution TraitSelection Miri.Interpreter
private def lift (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error

structure Selection where
  method : DefinitionIdentity
  arguments : Array Term
  slot : Nat
  deriving Repr, DecidableEq

private def uniqueTrait (context : AliasRuntime.Context) (identity : DefinitionIdentity) :
    Except String TraitDeclaration := do
  let rows := context.traits.traits.filter (·.definition == identity)
  unless rows.size == 1 do throw "object candidate trait source missing or ambiguous"
  let some row := rows[0]? | throw "object candidate trait source absent"
  pure row

/-- Confirm a ground direct-principal candidate and all supported nested clauses.
The implicit MetaSized bound is proved by the existing builtin solver. Other
nested clauses require the subsequent supertrait/projection implementation. -/
def select (work fuel : Nat) (method : MIR.DefId) (args : Array MIR.GenericArg) :
    RuntimeArrayTypes.CompilerM Selection := do
  let world ← get
  let identity ← lift (world.arena.identity method)
  let definitionRef ← lift (world.arena.definitionRef identity)
  let some definition := world.metadata.normalizationContext.generic.definitions[definitionRef]?
    | throw "object method raw definition absent"
  let some callable := definition.callableSource | throw "object method callable header absent"
  unless callable.definitionKind == "associated_function" && callable.container == some "trait" &&
      callable.hasSelf && callable.traitItem.isNone do
    throw "object method raw callable header inconsistent"
  let source ← lift (SourceEnvironmentRuntime.lookupDefinitions
    world.metadata.normalizationContext.generic.definitions identity)
  unless source.parent == source.genericParent do throw "object method source parents disagree"
  let some parent := source.genericParent | throw "object method source parent absent"
  unless source.ownPredicates.isEmpty do
    throw "object method own predicates require source fulfillment"
  let some (MIR.GenericArg.Type owner) := args[0]? | throw "object method canonical Self absent"
  let some view ← WorldDynamicData.query fuel owner | throw "object method Self is not dynamic"
  let some principal := view.principal | throw "object method requires a principal"
  unless principal.variables.isEmpty do throw "object candidate higher-ranked relation requires universe provider"
  if view.value.predicates.any (fun p => match p.body with | .projection .. => true | _ => false) then
    throw "object candidate projection obligations require source confirmation"
  let reference ← WorldDynamicData.principalRef fuel view
  unless reference.definition == parent.definition do
    throw "object candidate upcast requires supertrait confirmation"
  let context := world.metadata.normalizationContext
  let declaration ← lift (uniqueTrait context reference.definition)
  if declaration.implementations.any (·.isDefault) then
    throw "object candidate specialization requires source ordering"
  unless declaration.implementations.isEmpty do
    throw "object candidate competing impls require candidate winnowing"
  unless !declaration.isAuto && !declaration.isAlias &&
      declaration.parameters[0]? == some .type &&
      parent.parameterCount == declaration.parameters.size &&
      source.parameters.take parent.parameterCount == declaration.parameters do
    throw "object method canonical trait scope mismatch"
  let terms ← lift (GenericInstantiationWorld.ofArguments world.arena fuel args)
  unless terms.size == source.parameters.size do throw "object method argument arity mismatch"
  for (sort,term) in source.parameters.zip terms do
    unless sort == term.sort do throw "object method argument sort mismatch"
    lift (BinderRegions.validateClosed #[] fuel term)
  unless terms.take parent.parameterCount == reference.arguments do
    throw "object candidate trait arguments do not match principal"
  for (sort,term) in (source.parameters.zip terms).toList.drop parent.parameterCount do
    unless sort == .region && term == .atom .region "erased" "" do
      throw "object method own generics require instantiated lifetime-only scope"
  let members := declaration.members.filter (·.definition == identity)
  unless members.size == 1 do throw "object candidate method missing or ambiguous"
  let some member := members[0]? | throw "object candidate method absent"
  unless member.kind == "function" && member.isMethod && !member.isFinal do
    throw "object candidate final or nonmethod requires direct item provider"
  let nested ← lift (Substitution.clauses fuel reference.arguments declaration.superPredicates)
  for clause in nested do
    unless clause.variables.isEmpty do throw "object candidate nested binder requires universe provider"
    let .trait goal := clause.predicate | throw "object candidate nested predicate requires source confirmation"
    let nestedSource ← lift (uniqueTrait context goal.traitRef.definition)
    unless goal.polarity == .positive && nestedSource.builtin == some .metaSized &&
        goal.traitRef.arguments == #[view.source] do
      throw "object candidate explicit supertrait requires source confirmation"
    match ← lift (AliasRuntime.solveGoal context fuel work goal) with
    | .proven _ => pure ()
    | .noSolution => throw "object candidate nested obligation has no solution"
    | .ambiguous reason => throw s!"object candidate nested obligation ambiguous: {reason}"
  let methods ← lift (WorldDynMethods.ownMethods context work fuel reference.definition)
  let offsets := (methods.toList.zipIdx).filter (fun entry => entry.1 == identity)
  unless offsets.length == 1 do throw "object candidate method is not a unique eligible own slot"
  let some (_,offset) := offsets.head? | throw "object candidate own slot absent"
  pure ⟨identity,terms,3 + offset⟩

/-- Genuine ordinary Virtual syntax from confirmed source selection. -/
def ordinary (work fuel : Nat) (method : MIR.DefId) (args : Array MIR.GenericArg) :
    RuntimeArrayTypes.CompilerM InstanceId := do
  let selection ← select work fuel method args
  let definition ← lift ((← get).arena.definitionRef selection.method)
  RuntimeArrayTypes.internInstance (.Virtual definition selection.slot) args

/-- Same confirmed selection, then pinned expect_resolve_for_vtable Virtual
postprocessing. Body/ABI/vtable allocation are separate capabilities. -/
def forVTable (work fuel : Nat) (method : MIR.DefId) (args : Array MIR.GenericArg) :
    RuntimeArrayTypes.CompilerM InstanceId := do
  let selection ← select work fuel method args
  let world ← get
  let kcfi := world.metadata.source.producer.abiSession.map (fun s => s.sanitizers.contains "kcfi")
  let declaration ← lift (WorldVTableInstance.finishVirtual world.metadata.normalizationContext kcfi
    selection.method selection.arguments)
  WorldVTableInstance.intern fuel declaration
/-- Runtime source-call instance selection preserves ordinary non-object Item
construction. Trait methods with Dynamic Self must confirm an object candidate. -/
def resolveOrdinary (work fuel : Nat) (method : MIR.DefId) (args : Array MIR.GenericArg) :
    RuntimeArrayTypes.CompilerM InstanceId := do
  let world ← get
  let identity ← lift (world.arena.identity method)
  let reference ← lift (world.arena.definitionRef identity)
  let some definition := world.metadata.normalizationContext.generic.definitions[reference]?
    | throw "source callable definition absent"
  if definition.callableSource.bind (·.container) == some "trait" then
    let some (MIR.GenericArg.Type owner) := args[0]? | throw "ordinary trait method canonical Self absent"
    unless (← WorldDynamicData.query fuel owner).isSome do
      throw "ordinary concrete trait method requires source impl selection"
    return ← ordinary work fuel method args
  CompilerInstance.item method args

/-- Final VirtualCalls leaf dispatches Dynamic Self through confirmed source
object selection; concrete methods retain their existing source selection. -/
def resolveForVTable (work fuel : Nat) (method : MIR.DefId) (args : Array MIR.GenericArg) :
    RuntimeArrayTypes.CompilerM InstanceId := do
  let some (MIR.GenericArg.Type owner) := args[0]? | throw "virtual method canonical Self absent"
  match ← WorldDynamicData.query fuel owner with
  | some _ => forVTable work fuel method args
  | none => WorldVTableInstance.resolveMethod work fuel method args

end Miri.Input.WorldObjectCandidate
