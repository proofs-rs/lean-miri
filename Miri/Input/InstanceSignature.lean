import Miri.Input.RuntimeArrayTypes

/-! Raw function signature substitution for a complete execution instance.
Binder erasure, normalization, ABI classification and unwind policy are separate
operations. This module never consults an imported FnAbi query. -/
namespace Miri.Input.InstanceSignature
open GenericSubstitution

private def liftPure (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error

def instantiate (fuel : Nat) (instanceId : InstanceId) : RuntimeArrayTypes.CompilerM Term := do
  let world ← get
  let key ← liftPure do
    match ← world.instances.lookup instanceId with
    | .material key | .constructed key => pure key
  let .Item definition := key.kind | throw "raw ordinary signature requires an Item instance"
  unless (← liftPure (world.arena.identity definition)) == key.definition do
    throw "signature instance physical identity mismatch"
  let some source := world.metadata.source.definitions[definition]?
    | throw "raw signature definition is absent"
  let some material := source.genericTemplate
    | throw "raw generic signature template is absent"
  let arguments ← liftPure (GenericInstantiationWorld.ofArguments world.arena fuel key.arguments)
  liftPure (material.instantiateSignature fuel arguments)

end Miri.Input.InstanceSignature
