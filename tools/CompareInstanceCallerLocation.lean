import Miri.Input.TableTail
import Lean.Data.Json.Printer
import Miri.Input.CompilerRuntimeQueries

/-! Paired fresh pinned-rustc adapter. Baseline computed result rows are oracle
only. Candidate definition attributes and complete instance identity come from
its own export. Compiler definition identity establishes the crosswalk; names are not used. -/
open Lean Miri.Input Miri.Input.CompilerRuntimeQueries

-- Read just the exact instance/definition material; do not adapt unrelated ABI
-- or layout catalogs in either format.
private def readMaterial (source : String) (version : Nat) :
    Except String (Array DefinitionId × Array InstanceNode) := do
  let value ← Json.parse source
  unless (← (← value.getObjVal? "schema_version").getNat?) == version do
    throw "unexpected paired fixture schema"
  let definitions ← value.getObjVal? "definitions"
  let instances ← value.getObjVal? "instances"
  let definitions ← JsonReader.run
    (JsonReader.array (DecoderValues.parseDefinitionId "$caller.definitions")) definitions.compress
  let instances ← JsonReader.run
    (JsonReader.array (DecoderValues.parseInstance "$caller.instances")) instances.compress
  pure (definitions, instances)

-- This query reads only a variant, selected definition identity/attribute, or
-- ClosureOnce's embedded flag. Generic/type IDs are not its semantic inputs.
-- Project exactly those inputs before matching separately allocated catalogs;
-- this is a leaf-query comparison, not full instance-graph correspondence.
private def key (definitions : Array DefinitionId) (kind : Miri.Interpreter.CallInstanceKind) :
    Except String String := do
  let definitionKey (id : Nat) : Except String String := do
    let some definition := definitions[id]? | throw "definition absent from crosswalk"
    pure s!"{definition.crateIndex}:{definition.index}"
  match kind with
  | .Item id => return "item:" ++ (← definitionKey id)
  | .Virtual id slot => return s!"virtual:{← definitionKey id}:{slot}"
  | .Shim (.VTable id) => return "vtable:" ++ (← definitionKey id)
  | .Shim (.ClosureOnce callOnce closure flag) =>
    return s!"closure_once:{← definitionKey callOnce}:{← definitionKey closure}:{flag}"
  | .Intrinsic _ => pure "intrinsic:false"
  | .LlvmIntrinsic _ => pure "llvm_intrinsic:false"
  | .Shim shim => pure s!"constant_false_shim:{shimTag shim}"
where
  shimTag : Miri.Interpreter.CallShimKind → String
    | .VTable .. => "vtable" | .Reify .. => "reify" | .FnPtr .. => "fn_ptr"
    | .ClosureOnce .. => "closure_once" | .ConstructCoroutineInClosure .. => "construct_coroutine"
    | .ThreadLocal .. => "thread_local" | .FutureDropPoll .. => "future_drop_poll"
    | .DropGlue .. => "drop_glue" | .Clone .. => "clone" | .FnPtrAsPtr .. => "fn_ptr_as_ptr"
    | .FnPtrFromPtr .. => "fn_ptr_from_ptr" | .AsyncDropGlueCtor .. => "async_drop_ctor"
    | .AsyncDropGlue .. => "async_drop"

def main (args : List String) : IO UInt32 := do
  let [baselinePath, candidatePath] := args
    | throw (IO.userError "usage: compare_instance_caller BASELINE.json CANDIDATE.json")
  let baselineText ← IO.FS.readFile baselinePath
  let candidateText ← IO.FS.readFile candidatePath
  let result : Except String (Nat × Nat × Nat) := do
    let (baselineDefinitions, baselineInstances) ← readMaterial baselineText 12
    let (candidateDefinitions, candidateInstances) ← readMaterial candidateText 13
    let raw ← Json.parse baselineText
    let runtime ← raw.getObjVal? "compiler_runtime_queries"
    let rows ← (← runtime.getObjVal? "instances").getArr?
    let mut count := 0
    let mut trueCount := 0
    let mut falseCount := 0
    for row in rows do
      let id ← (← row.getObjVal? "instance_id").getNat?
      let expected ← (← row.getObjVal? "requires_caller_location").getBool?
      let some original := baselineInstances[id]? | throw "baseline instance absent"
      let wanted ← key baselineDefinitions original.instanceKind
      let mut matching := #[]
      for actual in candidateInstances do
        if (← key candidateDefinitions actual.instanceKind) == wanted then
          matching := matching.push actual
      unless !matching.isEmpty do throw s!"query-input crosswalk absent: {wanted}"
      let mut computed := false
      for actual in matching do
        computed ← instanceRequiresCallerLocation candidateDefinitions actual.instanceKind
        unless computed == expected do
          throw s!"query {wanted}: Lean={computed}, rustc={expected}"
      unless computed == expected do throw s!"instance {id}: Lean={computed}, rustc={expected}"
      count := count + 1
      if computed then trueCount := trueCount + 1 else falseCount := falseCount + 1
    unless count > 0 && trueCount > 0 && falseCount > 0 do
      throw "fixture must cover both caller-location outcomes"
    pure (count, trueCount, falseCount)
  match result with
  | .error error => throw (IO.userError error)
  | .ok (count, trueCount, falseCount) =>
    IO.println s!"{count} rustc/Lean requires_caller_location comparisons passed; true={trueCount}, false={falseCount}"
  return 0
