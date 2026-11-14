import Miri.Input.SourceEnvironment.Material
import Miri.Input.TraitSelection.Codec

namespace Miri.Input.SourceEnvironmentCodec
open Lean (Json)
open SourceEnvironment

private def keys (value : Json) (allowed : List String) : Except String Unit := do
  for (key, _) in (← value.getObj?).toArray do
    unless allowed.contains key do throw s!"unknown raw source environment field {key}"

private def readParent (rawParent : Json) : Except String (Option Parent) := do
  let parent ← if rawParent == .null then pure none else do
    keys rawParent ["definition", "parameter_count"]
    let definition ← GenericMaterialCodec.readDefinition (← rawParent.getObjVal? "definition")
    let parameterCount ← (← rawParent.getObjVal? "parameter_count").getNat?
    pure (some {definition, parameterCount})
  pure parent

def read (value : Json) : Except String Material := do
  keys value ["parameters", "predicate_parent", "generic_parent", "is_trait", "own_predicates"]
  let parameters ← (← (← value.getObjVal? "parameters").getArr?).mapM GenericMaterialCodec.readSort
  unless parameters.all (· != .aggregate) do throw "aggregate is not a source generic parameter sort"
  let parent ← readParent (← value.getObjVal? "predicate_parent")
  let genericParent ← readParent (← value.getObjVal? "generic_parent")
  if let some genericParent := genericParent then
    unless genericParent.parameterCount <= parameters.size do throw "source generic parent exceeds parameter domain"
  let isTrait ← (← value.getObjVal? "is_trait").getBool?
  if isTrait then
    unless parameters[0]? == some .type do throw "source trait scope has no type Self parameter"
  let ownPredicates ← TraitSelection.Codec.readClauses (← value.getObjVal? "own_predicates")
  TraitSelection.Codec.validateClauses parameters ownPredicates
  pure {parameters, parent, genericParent, isTrait, ownPredicates}
end Miri.Input.SourceEnvironmentCodec
