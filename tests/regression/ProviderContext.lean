import Miri.Input.Decoder
import Miri.Input.LowerMIR
import Miri.Input.CompilerProviders

open Miri Input

private def must {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error reason => throw (IO.userError reason)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def checkPools (source : LoweredProgram) (prepared : CompilerProviders.Prepared) : IO Unit := do
  check (prepared.program.bundle.spans == source.bundle.spans)
    "provider preparation changed canonical span IDs"
  check (prepared.program.bundle.definitions == source.bundle.definitions)
    "provider preparation changed canonical definition IDs"
  check (prepared.program.bundle.typeConstants == source.bundle.typeConstants)
    "provider preparation changed canonical type-constant IDs"

private def checkContext (context : LowerContext) (program : LoweredProgram) : IO Unit := do
  check (context.typeIds == program.input.types.map (·.id))
    "context uses different compiler type IDs"
  check (context.allocationIds == program.input.allocations.map (·.id))
    "context uses different allocation graph IDs"
  check (context.definitions == program.compilerTables.definitions)
    "context uses different compiler definitions"
  check (context.spans == program.compilerTables.spans)
    "context uses different compiler spans"
  check (context.typeConstants == program.compilerTables.typeConstants)
    "context uses different type constants"
  for id in context.typeIds do
    check (context.containsTypeId id) "context lost a declared type ID"
  check (!context.containsTypeId program.input.types.size)
    "context accepts a type ID beyond its compilation-local pool"
  check (!context.containsAllocationId program.input.allocations.size)
    "context accepts an allocation ID beyond its compilation-local pool"

private def checkRuntime (runtime : RuntimeMetadata) (program : LoweredProgram) : IO Unit := do
  for source in program.input.types do
    let node ← match runtime.node source.id with
      | .ok node => pure node
      | .error reason => throw (IO.userError (toString reason))
    check (node.id == source.id && node.layoutId == source.layoutId && node.shapeKind == source.shapeKind)
      "runtime type lookup differs from its program's compiler type definition"

def main (args : List String) : IO Unit := do
  let [firstPath, secondPath] := args
    | throw (IO.userError "usage: ProviderContextTests <root-u32> <control-flow>")
  let first ← must (decodeJson (← IO.FS.readFile firstPath))
  let second ← must (decodeJson (← IO.FS.readFile secondPath))
  let firstProgram ← must (lowerProgram first.document)
  let secondProgram ← must (lowerProgram second.document)
  let prepared ← must (CompilerProviders.prepare firstProgram)
  let secondPrepared ← must (CompilerProviders.prepare secondProgram)
  checkPools firstProgram prepared
  checkPools secondProgram secondPrepared
  checkContext prepared.loweringContext prepared.program
  checkRuntime prepared.runtime prepared.program
  checkContext secondPrepared.loweringContext secondPrepared.program
  checkRuntime secondPrepared.runtime secondPrepared.program
  let nested := secondPrepared.lifecycle.calls.symbols.facts.context
  let independentNested : CompilerFacts.Context := { nested with lowering := none }
  checkContext independentNested.loweringContext secondPrepared.program
  checkRuntime independentNested.runtime secondPrepared.program
  let otherFacts := { prepared.lifecycle.calls.symbols.facts with context := independentNested }
  let otherSymbols := { prepared.lifecycle.calls.symbols with facts := otherFacts }
  let otherCalls := { prepared.lifecycle.calls with symbols := otherSymbols }
  let otherLifecycle := { prepared.lifecycle with calls := otherCalls }
  let manualProvider := { prepared with lifecycle := otherLifecycle, lowering := none }
  checkContext manualProvider.loweringContext prepared.program
  checkContext manualProvider.lifecycle.calls.symbols.facts.context.loweringContext secondPrepared.program
  checkRuntime manualProvider.runtime prepared.program
  checkRuntime manualProvider.lifecycle.calls.symbols.facts.context.runtime secondPrepared.program
  let rebound := { independentNested with runtime := prepared.runtime }.withProgram prepared.program
  checkContext rebound.loweringContext prepared.program
  checkRuntime rebound.runtime prepared.program
  IO.println "canonical provider pools, compilation-local context bounds and independent runtime contexts PASS"
