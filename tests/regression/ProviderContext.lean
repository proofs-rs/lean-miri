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

private def checkInlineLookup (prepared : CompilerProviders.Prepared) : IO Unit := do
  let pointers := prepared.pointers
  let records := pointers.calls.calls.program.input.queries.runtime.instances
  for row in records do
    check (CompilerFunctionPointers.inlineNeverUsing pointers.inlineLookup row.instanceId ==
      some row.inlineNever) "prepared inline lookup differs from source row"
  let missing := pointers.calls.calls.program.input.instances.size
  check (CompilerFunctionPointers.inlineNeverUsing pointers.inlineLookup missing == none)
    "prepared inline lookup accepts absent instance"
  let some row := records[0]?
    | throw (IO.userError "inline lookup fixture lacks runtime instances")
  do
    let replaceRecords := fun rows =>
      let program := pointers.calls.calls.program
      let input := program.input
      let input := {input with queries := {input.queries with runtime :=
        {input.queries.runtime with instances := rows}}}
      {pointers.calls with calls := {pointers.calls.calls with program := {program with input}}}
    let empty ← must (CompilerFunctionPointers.prepare (replaceRecords #[]))
    check (CompilerFunctionPointers.inlineNeverUsing empty.inlineLookup row.instanceId == none)
      "inline lookup invents missing metadata for a valid instance"
    for value in [false, true] do
      let isolated ← must (CompilerFunctionPointers.prepare
        (replaceRecords #[{row with inlineNever := value}]))
      check (CompilerFunctionPointers.inlineNeverUsing isolated.inlineLookup row.instanceId == some value)
        "inline lookup reused metadata from another preparation"
      check (CompilerFunctionPointers.inlineNeverUsing pointers.inlineLookup row.instanceId ==
        some row.inlineNever) "independent inline preparation mutated original lookup"
    let duplicate ← must (CompilerFunctionPointers.prepare (replaceRecords (records.push row)))
    check (CompilerFunctionPointers.inlineNeverUsing duplicate.inlineLookup row.instanceId ==
      some row.inlineNever) "equal duplicate inline attribute changed lookup"
    match CompilerFunctionPointers.prepare
        (replaceRecords (records.push {row with inlineNever := !row.inlineNever})) with
    | .error reason =>
      check (reason == "conflicting exact full-instance inline attribute")
        "conflicting inline attribute changed error"
    | .ok _ => throw (IO.userError "conflicting inline attribute accepted")
    let absent := {row with instanceId := missing}
    match CompilerFunctionPointers.prepare (replaceRecords (records.push absent)) with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "inline attribute for absent source instance accepted")

def main (args : List String) : IO Unit := do
  let [firstPath, secondPath] := args
    | throw (IO.userError "usage: ProviderContextTests <root-u32> <control-flow>")
  let first ← must (decodeJson (← IO.FS.readFile firstPath))
  let second ← must (decodeJson (← IO.FS.readFile secondPath))
  let firstProgram ← must (lowerProgram first.document)
  let secondProgram ← must (lowerProgram second.document)
  let prepared ← must (CompilerProviders.prepare firstProgram)
  let secondPrepared ← must (CompilerProviders.prepare secondProgram)
  checkInlineLookup prepared
  checkInlineLookup secondPrepared
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
