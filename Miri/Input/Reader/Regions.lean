import Miri.Input.Reader.MIRState
import Miri.Input.Reader.Table
import Miri.Input.CompilerTables

namespace Miri.Input.Reader.RegionReader
open Lean Miri.MIR

abbrev State := MIRReader.State
abbrev Decode := MIRReader.Decode

def definitionValue (id : DefinitionId) : Decode DefId := do
  let state ← get
  let key := (id.crateIndex, id.index)
  if let some index := state.definitions[key]? then return index
  let index := state.compiler.definitions.size
  set {state with
    compiler := {state.compiler with definitions := state.compiler.definitions.push id}
    definitions := state.definitions.insert key index}
  return index

def definition (catalog : Catalog) (input : Json) (path : String) : Decode DefId := do
  definitionValue ⟨← catalog.natural (← catalog.field input "crate" path) path,
    ← catalog.natural (← catalog.field input "index" path) path⟩

def boundIndex (catalog : Catalog) (input : Json) (path : String) : Except String BoundVarIndexKind := do
  match ← catalog.string (← catalog.field input "kind" path) path with
  | "bound" => return .Bound (← catalog.natural (← catalog.field input "debruijn_index" path) path)
  | "canonical" => return .Canonical
  | kind => throw s!"{path}: unsupported bound index kind {kind}"

private def boundRegion (catalog : Catalog) (input : Json) (path : String) : Decode BoundRegionKind := do
  let field := fun key => catalog.field input key path
  match ← catalog.string (← field "kind") path with
  | "anonymous" => return .Anon
  | "named_for_printing" => return .NamedForPrinting (← catalog.string (← field "name") path)
  | "named" => return .Named (← definition catalog (← field "def_id") path)
  | "closure_environment" => return .ClosureEnv
  | kind => throw s!"{path}: unsupported bound region kind {kind}"

private def value (catalog : Catalog) (input : Json) (path : String) : Decode Region := do
  catalog.requireSupported input path
  let field := fun key => catalog.field input key path
  let natural := fun key => do catalog.natural (← field key) path
  match ← catalog.string (← field "kind") path with
  | "early_parameter" => return .EarlyParameter (← natural "index") (← catalog.string (← field "name") path)
  | "bound" =>
    return .Bound (← boundIndex catalog (← field "index_kind") path)
      (← natural "variable_index") (← boundRegion catalog (← field "bound_kind") path)
  | "late_parameter" =>
    let parameter ← field "parameter"
    let parameterField := fun key => catalog.field parameter key path
    let kind ← (show Decode LateParamRegionKind from do
      match ← catalog.string (← parameterField "kind") path with
      | "anonymous" => return .Anon (← catalog.natural (← parameterField "index") path)
      | "named_anonymous" =>
        return .NamedAnon (← catalog.natural (← parameterField "index") path)
          (← catalog.string (← parameterField "name") path)
      | "named" => return .Named (← definition catalog (← parameterField "def_id") path)
      | "closure_environment" => return .ClosureEnv
      | tag => throw s!"{path}: unsupported late parameter region {tag}")
    return .LateParameter (← definition catalog (← field "scope_def_id") path) kind
  | "static" => return .Static
  | "inference_variable" => return .InferenceVariable (← natural "index")
  | "placeholder" =>
    return .Placeholder (← natural "universe") (← natural "variable_index")
      (← boundRegion catalog (← field "bound_kind") path)
  | "erased" => return .Erased
  | "error" => return .Error
  | kind => throw s!"{path}: unsupported region kind {kind}"

def region (catalog : Catalog) (input : Json) (path : String) : Decode Nat :=
  catalog.readCached (·.regions) (fun state regions => {state with regions})
    (value catalog) input path

end Miri.Input.Reader.RegionReader
