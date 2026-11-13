import Miri.Input.WorldVTableMethods
import Miri.Input.CompilerInstance

/-! Ground, unique ordinary associated-function selection from raw declarations.
Pinned rustc_ty_utils/src/instance.rs resolve_associated_item UserDefined arm:
select and fulfill an impl, find its final associated leaf, rebase method args,
erase regions and return Item. No vtable or track-caller shim postprocessing.
Specialization ancestry, trait defaults and builtin candidates remain explicit
residuals. Signature comparison is a deliberately exact supported subset of
compare_impl_item, never a substitute for missing compatibility evidence. -/
namespace Miri.Input.WorldOrdinaryTraitInstance
open GenericSubstitution TraitSelection Miri.Interpreter
private def lift (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error e => throw e

private def definition (context : AliasRuntime.Context) (identity : DefinitionIdentity) :
    Except String DefinitionId := do
  let reference ← GenericInstantiation.definitionRef context.generic identity
  let some source := context.generic.definitions[reference]?
    | throw "ordinary trait raw definition absent"
  pure source

private def callable (context : AliasRuntime.Context) (identity : DefinitionIdentity)
    (container : String) : Except String (SourceEnvironment.Material × CallableSource × Term) := do
  let source ← definition context identity
  let some header := source.callableSource | throw "ordinary trait callable header absent"
  unless header.definitionKind == "associated_function" && header.container == some container do
    throw "ordinary trait callable source container mismatch"
  let some scope := source.sourceEnvironment | throw "ordinary trait callable scope absent"
  unless scope.parent == scope.genericParent do throw "ordinary trait callable source parents disagree"
  let some template := source.genericTemplate | throw "ordinary trait callable template absent"
  unless template.parameters == scope.parameters && template.fields.isEmpty do
    throw "ordinary trait callable template canonical scope mismatch"
  let .definition .type "function_definition" owner _ := template.typeExpression
    | throw "ordinary trait callable template is not FnDef"
  unless owner == identity do throw "ordinary trait callable template physical identity mismatch"
  let some signature := template.signatureExpression | throw "ordinary trait callable raw signature absent"
  pure (scope,header,signature)

private def normalizedArguments (context : AliasRuntime.Context) (work fuel : Nat)
    (parameters : Array ArgSort) (arguments : Array Term) : Except String (Array Term) := do
  unless parameters.size == arguments.size do throw "ordinary trait argument arity mismatch"
  (parameters.zip arguments).mapM fun (sort,argument) => do
    unless sort == argument.sort do throw "ordinary trait argument sort mismatch"
    Match.requireGround fuel argument
    let erased ← BinderRegions.eraseAndAnonymize fuel argument
    AliasRuntime.normalizeTerm context work fuel #[] #[] erased

private def fulfill (context : AliasRuntime.Context) (work fuel : Nat)
    (identity : DefinitionIdentity) (arguments : Array Term) : Except String Unit := do
  let clauses ← SourceEnvironment.instantiate
    (SourceEnvironmentRuntime.lookupDefinitions context.generic.definitions) fuel identity arguments
  let hooks := AliasRuntime.traitHooks context fuel (fun universeIndex remaining goals term =>
    AliasRuntime.normalizeTermScoped context universeIndex work remaining #[] goals term)
  match ← TraitSelection.fulfill context.traits hooks {eraseRegions := true} fuel work clauses with
  | .proven _ => pure ()
  | .noSolution => throw "ordinary trait source predicates have no solution"
  | .ambiguous reason => throw s!"ordinary trait source predicates ambiguous: {reason}"

private def signature (context : AliasRuntime.Context) (work fuel : Nat)
    (raw : Term) (arguments : Array Term) : Except String RawFunctionSignature.Signature := do
  let instantiated ← GenericSubstitution.instantiate fuel arguments raw
  let signature ← RawFunctionSignature.read instantiated
  unless BinderRegions.regionOnly signature.variables do
    throw "ordinary trait signature type/const binder requires compatibility provider"
  let normalize := fun term => do
    let opened ← Universes.openTerm signature.variables 1 fuel 0 term
    let erased ← BinderRegions.eraseAndAnonymize fuel opened
    AliasRuntime.normalizeTerm context work fuel #[] #[] erased
  pure {signature with
    variables := #[]
    inputs := ← signature.inputs.mapM normalize
    output := ← normalize signature.output}

/-- Only fully ground, uniquely selected final impl methods are admitted.
The source method scope owns the inherited trait prefix; the chosen impl owns
its inferred substitution prefix. The original method's own arguments survive
exactly once after that prefix is replaced. -/
def resolve (work fuel : Nat) (method : MIR.DefId) (args : Array MIR.GenericArg) :
    RuntimeArrayTypes.CompilerM InstanceId := do
  let world ← get
  let context := world.metadata.normalizationContext
  let identity ← lift (world.arena.identity method)
  let (scope,header,rawSignature) ← lift (callable context identity "trait")
  unless header.traitItem.isNone && header.hasSelf do throw "ordinary trait declaration maps to another trait item"
  let some parent := scope.genericParent | throw "ordinary trait method parent absent"
  let parentScope ← lift (SourceEnvironmentRuntime.lookupDefinitions context.generic.definitions parent.definition)
  let declarations := context.traits.traits.filter (·.definition == parent.definition)
  unless declarations.size == 1 do throw "ordinary trait source missing or ambiguous"
  let some declaration := declarations[0]? | throw "ordinary trait source absent"
  unless parentScope.isTrait && parentScope.parent == parentScope.genericParent &&
      parentScope.parameters == declaration.parameters && declaration.parameters[0]? == some .type &&
      parent.parameterCount == declaration.parameters.size &&
      scope.parameters.take parent.parameterCount == declaration.parameters do
    throw "ordinary trait canonical generic parent mismatch"
  unless !declaration.isAlias && !declaration.isAuto && declaration.builtin.isNone do
    throw "ordinary trait builtin or alias requires source selection provider"
  if declaration.implementations.any (·.isDefault) then
    throw "ordinary trait specialization requires source ancestry"
  let members := declaration.members.filter (·.definition == identity)
  unless members.size == 1 do throw "ordinary trait associated member missing or ambiguous"
  let some member := members[0]? | throw "ordinary trait associated member absent"
  unless member.kind == "function" do
    throw "ordinary trait associated member callable mismatch"
  let rawArguments ← lift (GenericInstantiationWorld.ofArguments world.arena fuel args)
  let arguments ← lift (normalizedArguments context work fuel scope.parameters rawArguments)
  let reference : TraitRef := ⟨parent.definition,arguments.take parent.parameterCount⟩
  let selection ← lift (AliasRuntime.selectGoal context fuel work reference)
  let implementations := declaration.implementations.filter (·.definition == selection.implementation)
  unless implementations.size == 1 do throw "ordinary trait selected impl source missing or ambiguous"
  let some implementation := implementations[0]? | throw "ordinary trait selected impl source absent"
  unless implementation.polarity == .positive && !implementation.isDefault do
    throw "ordinary trait selected impl is negative or specialized"
  let implScope ← lift (SourceEnvironmentRuntime.lookupDefinitions context.generic.definitions implementation.definition)
  unless !implScope.isTrait && implScope.parent == implScope.genericParent &&
      implScope.parameters == implementation.parameters do
    throw "ordinary trait selected impl canonical scope mismatch"
  let substitution ← lift (normalizedArguments context work fuel implementation.parameters selection.substitution)
  let methods := implementation.methods.filter (·.traitAssociatedDefinition == identity)
  if methods.isEmpty then throw "ordinary trait default method requires source ancestry"
  unless methods.size == 1 do throw "ordinary trait selected method source ambiguous"
  let some selected := methods[0]? | throw "ordinary trait selected method absent"
  unless selected.isFinal do throw "ordinary trait selected method specialization requires source leaf provider"
  let (selectedScope,selectedHeader,selectedSignature) ← lift
    (callable context selected.implementationDefinition "trait_impl")
  let some selectedParent := selectedScope.genericParent | throw "ordinary trait impl method parent absent"
  unless selectedParent.definition == implementation.definition &&
      selectedParent.parameterCount == implementation.parameters.size &&
      selectedScope.parameters.take selectedParent.parameterCount == implementation.parameters &&
      selectedHeader.traitItem == some identity && !selectedHeader.hasSelf do
    throw "ordinary trait selected method canonical owner mismatch"
  let rebased := substitution ++ arguments.extract parent.parameterCount arguments.size
  let rebased ← lift (normalizedArguments context work fuel selectedScope.parameters rebased)
  lift (fulfill context work fuel identity arguments)
  lift (fulfill context work fuel selected.implementationDefinition rebased)
  let expected ← lift (signature context work fuel rawSignature arguments)
  let actual ← lift (signature context work fuel selectedSignature rebased)
  unless expected == actual do throw "ordinary trait selected method signature compatibility requires source provider"
  let definition ← lift (world.arena.definitionRef selected.implementationDefinition)
  let physical ← RuntimeArrayTypes.liftType (GenericInstantiationWorld.resolveArguments fuel rebased)
  CompilerInstance.item definition physical
end Miri.Input.WorldOrdinaryTraitInstance
