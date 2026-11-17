import Miri.Input.CompilerProviders

open Miri.Input Miri.Interpreter

example (runtime : RuntimeMetadata) (id : TypeId) :
    runtime.startSession.lookup id = runtime.lookup id :=
  RuntimeMetadata.startSession_lookup runtime id

example (prepared : CompilerInstanceAbi.Prepared) (callee : CallInstance) (extra : Array TypeId) :
    CompilerInstanceAbi.abiOfInstance prepared callee extra =
      SourceAbiRuntime.ofInstance prepared.runtime callee extra :=
  CompilerInstanceAbi.abiOfInstance_eq prepared callee extra

example (context : CompilerFacts.Context) (id : TypeId) (query : String) :
    CompilerFacts.boolean context id query = ConcreteTypeQueries.boolean context.runtime id query := rfl

example (context : CompilerFacts.Context) (id : TypeId) (query : String) :
    CompilerFacts.requiredType context id query = (do
      let some ty ← ConcreteTypeQueries.optionalType context.runtime id query
        | throw s!"compiler query {query} returned None"
      pure ty) := rfl
