import Miri.Input.Decoder
import Miri.Input.LowerMIR
import Miri.Input.CompilerProviders

open Lean Miri.Input

private def must {α} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error reason => throw (IO.userError reason)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def renderResult {α} (value : Except String α) [Repr α] : String :=
  match value with
  | .error reason => s!"error:{reason}"
  | .ok result => s!"ok:{reprStr result}"

def main (args : List String) : IO Unit := do
  let [firstPath, secondPath] := args
    | throw (IO.userError "usage: ProviderPrimitiveRebinding <root-u32> <root-control-flow>")
  let firstDecoded ← must (decodeJson (← IO.FS.readFile firstPath))
  let secondDecoded ← must (decodeJson (← IO.FS.readFile secondPath))
  let firstProgram ← must (lowerProgram firstDecoded.document)
  let secondProgram ← must (lowerProgram secondDecoded.document)
  let firstProvider ← must (CompilerProviders.prepare firstProgram)
  let secondProvider ← must (CompilerProviders.prepare secondProgram)

  let firstOwnCaller := firstProvider.callerLocationType
  let secondOwnCaller := secondProvider.callerLocationType
  check (firstOwnCaller.toOption == some 21 && secondOwnCaller.toOption == some 22)
    "genuine source caller-location IDs changed"
  let firstUsize := firstProvider.primitiveLayout "usize"
  let secondUsize := secondProvider.primitiveLayout "usize"
  check (firstUsize.toOption.map (·.ty) == some 13 && secondUsize.toOption.map (·.ty) == some 14)
    "genuine source usize identities changed"

  check (renderResult (CompilerPrimitiveFacts.primitiveLayout secondProvider.runtime "usize") ==
    renderResult (secondProvider.primitiveLayout "usize"))
    "provider primitive result diverged from its requested runtime"

  -- Give the provider a nested facts context from another source whose runtime
  -- has missing query evidence. The provider's own primitive source remains
  -- source2, and its query must preserve that result/error boundary.
  let malformedNestedRuntime : RuntimeMetadata := { firstProvider.runtime with
    source := { firstProvider.runtime.source with raw := .null } }
  let malformedNestedIndexed := RuntimeMetadata.Indexed.ofMetadata malformedNestedRuntime
  let originalNested := secondProvider.lifecycle.calls.symbols.facts.context
  let malformedNested : CompilerFacts.Context := { originalNested with
    runtime := malformedNestedIndexed
    program := firstProgram
    lowering := none
  }
  let nestedCallerError :=
    CompilerPrimitiveFacts.callerLocationType malformedNested.runtime.toRuntimeMetadata
  match nestedCallerError with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "malformed wrong-source nested context unexpectedly resolved")
  let wrongFacts := { secondProvider.lifecycle.calls.symbols.facts with context := malformedNested }
  let wrongSymbols := { secondProvider.lifecycle.calls.symbols with facts := wrongFacts }
  let wrongCalls := { secondProvider.lifecycle.calls with symbols := wrongSymbols }
  let wrongLifecycle := { secondProvider.lifecycle with calls := wrongCalls }
  let manualProvider := { secondProvider with lifecycle := wrongLifecycle }
  check (renderResult manualProvider.callerLocationType == renderResult secondOwnCaller)
    "provider primitive query followed a malformed nested context instead of its requested runtime"
  check (renderResult (manualProvider.primitiveLayout "usize") == renderResult secondUsize)
    "provider primitive query followed the wrong nested source"

  let missingKey := "qa_missing_primitive"
  let directMissing := CompilerPrimitiveFacts.primitiveLayout secondProvider.runtime missingKey
  let cachedMissing := secondProvider.primitiveLayout missingKey
  let reboundMissing := manualProvider.primitiveLayout missingKey
  check (renderResult directMissing == renderResult cachedMissing &&
    renderResult directMissing == renderResult reboundMissing)
    "provider/nested-source missing-query error precedence changed"
  check (renderResult nestedCallerError != renderResult directMissing)
    "wrong-source malformed error unexpectedly collapsed into the requested missing-query error"

  IO.println s!"provider primitive rebinding PASS: ownCaller={renderResult secondOwnCaller}, wrongNested={renderResult nestedCallerError}, ownUsize={renderResult secondUsize}, missing={renderResult directMissing}"
