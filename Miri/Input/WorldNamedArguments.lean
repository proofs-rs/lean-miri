import Miri.Input.GenericInstantiationWorld

/-! rustc_middle/ty/generics.rs::own_args_no_defaults uses structural equality
of instantiated raw defaults, walking only the contiguous trailing suffix.
This is a printing operation, not normalization or default type inference. -/
namespace Miri.Input.WorldNamedArguments
open TypeArena

def own (world : World) (fuel : Nat) (path : DefinitionPath.Material)
    (arguments : Array MIR.GenericArg) : Except String (Array MIR.GenericArg) := do
  unless path.parentParameterCount == 0 do
    throw "inherited generic definition-path arguments are not implemented"
  unless path.parameterDefaults.size == arguments.size do
    throw "definition-path argument count differs from raw generic header"
  unless path.parameterDefaults.any (fun value => value) do return arguments
  let some defaults := path.parameterDefaultExpressions
    | throw "generic default elision requires raw declaration default expressions"
  unless defaults.size == arguments.size do throw "generic default expression count mismatch"
  let terms ← GenericInstantiationWorld.ofArguments world fuel arguments
  let mut count := arguments.size
  for index in (List.range arguments.size).reverse do
    let some expression := defaults[index]? | throw "generic default expression absent"
    let some expression := expression | break
    let expected ← GenericSubstitution.instantiate fuel terms expression
    let some actual := terms[index]? | throw "generic actual argument absent"
    unless expected == actual do break
    count := index
  pure (arguments.extract 0 count)
end Miri.Input.WorldNamedArguments
