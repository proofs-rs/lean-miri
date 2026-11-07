import Miri.Input.Reader.Instances
import Miri.Input.CompilerExternAbi

namespace Miri.Input.Reader.FunctionReader
open Lean Miri.MIR Miri.Interpreter
abbrev Decode := MIRReader.Decode

private def typeId (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Except String TyId := do
  let id ← catalog.natural (← catalog.field input "type_id" path) path
  unless id < count do throw s!"{path}: invalid function type ID {id}"
  return id

def externAbi (catalog : Catalog) (input : Json) (path : String) : Except String ABI.ExternAbi := do
  catalog.requireSupported input path
  let kind ← catalog.string (← catalog.field input "kind" path) path
  let input ← catalog.inspect (← catalog.field input "unwind" path) path
  let unwind ← if input == .null then pure none else some <$> catalog.boolean input path
  CompilerExternAbi.ofFields kind unwind

def typeData (catalog : Catalog) (count : Nat) (evidence : Option DefinitionId)
    (input : Json) (path : String) : Decode (Option FunctionTypeData) := do
  let shape ← catalog.field input "shape" path
  let kind ← catalog.string (← catalog.field shape "kind" path) path
  unless kind == "function_definition" || kind == "closure" do return none
  catalog.requireSupported shape path
  let some evidence := evidence | throw s!"{path}: compiler definition evidence absent"
  let definition ← RegionReader.definitionValue evidence
  let id ← GenericReader.arguments catalog count (← catalog.field shape "generic_args" path) path
  let state ← get
  let args ← state.arguments.lookup id |>.mapError (fun id => s!"{path}: missing function arguments {id}")
  return some ⟨definition,args⟩

private def signature (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Except String (Nat × ABI.ExternAbi) := do
  catalog.requireSupported input path
  let value ← catalog.field input "value" path
  let inputs ← catalog.array (← catalog.field value "inputs" path) path
  for input in inputs do let _ ← typeId catalog count input path; pure ()
  let _ ← typeId catalog count (← catalog.field value "output" path) path
  return (inputs.size, ← externAbi catalog (← catalog.field value "abi" path) path)

private def query (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Decode (TypeId × FunctionQueryData) := do
  unless (← catalog.string (← catalog.field input "typing_env" path) path) == "fully_monomorphized" do
    throw s!"{path}: function query environment mismatch"
  let ty ← catalog.natural (← catalog.field input "type_id" path) path
  unless ty < count do throw s!"{path}: invalid function query type ID {ty}"
  let source ← catalog.field input "function_kind" path
  let kind ← match ← catalog.string (← catalog.field source "kind" path) path with
    | "function_pointer" => pure CallFunctionKind.FnPtr
    | "function_definition" => do
      let value ← InstanceReader.read catalog count source path
      let .Item definition := value.kind | throw s!"{path}: FnDef kind is not an Item"
      pure (.FnDef definition value.args)
    | kind => throw s!"{path}: unsupported function kind {kind}"
  let input ← catalog.field input "signature_query" path
  return (ty, ⟨kind, signature catalog count input path⟩)

def queries (catalog : Catalog) (count : Nat) : Decode (Array (Option FunctionQueryData)) := do
  let source ← catalog.field catalog.root "compiler_function_facts" "$"
  let values ← catalog.array (← catalog.field source "types" "$.compiler_function_facts") "$.compiler_function_facts.types"
  let mut result := Array.replicate count none
  for (input,index) in values.toList.zipIdx do
    let (ty,value) ← query catalog count input s!"$.compiler_function_facts.types[{index}]"
    if bound : ty < result.size then
      unless result[ty].isNone do throw s!"duplicate function query for type {ty}"
      result := result.set ty (some value) bound
    else throw s!"invalid function query type ID {ty}"
  return result

end Miri.Input.Reader.FunctionReader
