import Miri.Input.RuntimeArrayTypes

/-! Raw function signature substitution for a complete execution instance.
Binder erasure, normalization, ABI classification and unwind policy are separate
operations. This module never consults an imported FnAbi query. -/
namespace Miri.Input.InstanceSignature
open GenericSubstitution

private def liftPure (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error

/-- Instantiate the physical declaration with its complete ordered arguments.
No instance selection or imported signature answer is required. -/
def instantiateDefinition (fuel : Nat) (definition : DefinitionRef)
    (arguments : Array Miri.MIR.GenericArg) : RuntimeArrayTypes.CompilerM Term := do
  let world ← get
  let _ ← liftPure (world.arena.identity definition)
  let some source := world.metadata.source.definitions[definition]?
    | throw "raw signature definition is absent"
  let some callable := source.callableSource
    | throw "raw signature callable source header is absent"
  unless callable.definitionKind == "function" || callable.definitionKind == "associated_function" do
    throw "raw signature definition is not a function"
  let some material := source.genericTemplate
    | throw "raw generic signature template is absent"
  let arguments ← liftPure (GenericInstantiationWorld.ofArguments world.arena fuel arguments)
  liftPure (material.instantiateSignature fuel arguments)

def instantiate (fuel : Nat) (instanceId : InstanceId) : RuntimeArrayTypes.CompilerM Term := do
  let world ← get
  let key ← liftPure do
    match ← world.instances.lookup instanceId with
    | .material key | .constructed key => pure key
  let definition ← match key.kind with
    | .Item definition | .Virtual definition _ => pure definition
    | _ => throw "raw signature requires an Item or Virtual instance"
  unless (← liftPure (world.arena.identity definition)) == key.definition do
    throw "signature instance physical identity mismatch"
  instantiateDefinition fuel definition key.arguments

end Miri.Input.InstanceSignature
