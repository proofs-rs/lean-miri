import Miri.Input.AbiConversion
import Miri.Input.CompilerInstance
import Miri.Input.CallCompatibility
import Miri.ABI.FnAbi
import Miri.Interpreter.Call

/-! Conversion of canonical ABI records and exact existing body ownership.
Call-site answer arrays are not prepared here: normal runtime Item resolution
and body/ABI demands use the persistent source compiler World. -/
namespace Miri.Input.CallResolution
open Lean Miri.ABI Miri.Interpreter
abbrev Result := Except String
private def require (value : Option A) (message : String) : Result A :=
  match value with | some value => pure value | none => throw message
abbrev convention := AbiConversion.convention
abbrev functionAbi := AbiConversion.functionAbi
abbrev functionAbiId := AbiConversion.functionAbiId


structure InstanceBody where
  fnInstance : CallInstance
  sourceInstanceId : InstanceId
  bodyIndex : Nat
structure Prepared where
  program : LoweredProgram
  runtime : RuntimeMetadata
  bodies : Array InstanceBody
  obligations : Array Obligation

/-- Retain only canonical instance/body ownership for existing input. Callee
selection and ABI requests run against the live source World; preparation never
requires, enumerates or caches call-site resolution answers. -/
private def prepareUsingRuntime (_profile : Lean.Options) (program : LoweredProgram) (runtime : RuntimeMetadata) :
    Result Prepared := do
  let instances := program.input.instances
  let mut bodies := #[]
  let mut obligations := #[]
  for (sourceId,index) in program.instances do
    match CompilerInstance.source instances sourceId with
    | .error message => obligations := obligations.push ⟨s!"instance[{sourceId}]",message⟩
    | .ok _ => bodies := bodies.push ⟨sourceId,sourceId,index⟩
  return ⟨program.withCompilerTables program.compilerTables,runtime,bodies,obligations⟩

/-- Prepare canonical body ownership using the already validated immutable
runtime metadata for this program's unchanged ImportDocument. Compiler tables
may grow during preparation, but `CompilerGlobals.prepareProgram` changes only
the lowered bundle and leaves that document untouched. -/
def prepareWithRuntimeProfiled (profile : Lean.Options) (runtime : RuntimeMetadata) (program : LoweredProgram) : Result Prepared := do
  let program := profileit "prepare.compiler_globals" profile fun _ => CompilerGlobals.prepareProgram program
  prepareUsingRuntime profile program runtime

/-- Prepare canonical body ownership using validated runtime metadata. -/
def prepareWithRuntime (runtime : RuntimeMetadata) (program : LoweredProgram) : Result Prepared :=
  prepareWithRuntimeProfiled {} runtime program

/-- Validate target metadata before preparing canonical body ownership. -/
def prepare (program : LoweredProgram) : Result Prepared := do
  let program := CompilerGlobals.prepareProgram program
  let runtime ← (RuntimeMetadata.ofDocument program.input).mapError toString
  prepareUsingRuntime {} program runtime

/-- A loaded body carries the exact source table key. Equal MIR syntax does
not make distinct root/template/promoted/instance body identities interchangeable. -/
def loadedBodyOfInstance (prepared : Prepared) (fnInstance : CallInstance) : Result LoadedBody := do
  let matching := prepared.bodies.filter (·.fnInstance == fnInstance)
  unless matching.size == 1 do
    throw s!"missing or ambiguous canonical instance body identity: requested={reprStr fnInstance}, matches={matching.size}"
  let some candidate := matching[0]? | throw "compiler instance body is unavailable"
  let source ← require prepared.program.input.instances[candidate.sourceInstanceId]?
    "canonical source instance record is missing"
  unless source.kind == .instanceMir do throw "compiler body is not a substituted executable instance"
  let body ← require prepared.program.bundle.bodies[candidate.bodyIndex]? "instance body index is absent"
  unless body.input.instanceId == candidate.sourceInstanceId do throw "instance/body identity mismatch"
  unless body.obligations.isEmpty do throw "lowered instance body has unresolved obligations"
  return ⟨.ofCanonicalIndex candidate.bodyIndex, body.body⟩

end Miri.Input.CallResolution
