import Miri.Input.Reader.Generics

namespace Miri.Input.Reader.RuntimeQueryReader
open Lean Miri.MIR
abbrev Decode := MIRReader.Decode

private def environment (catalog : Catalog) (input : Json) (path : String) : Except String Unit := do
  unless (← catalog.string (← catalog.field input "typing_env" path) path) == "fully_monomorphized" do
    throw s!"{path}: runtime query typing environment mismatch"

private def typeId (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Except String Nat := do
  let id ← catalog.natural (← catalog.field input "type_id" path) path
  unless id < count do throw s!"{path}: invalid runtime query type {id}"
  return id

private def instanceId (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Except String Nat := do
  let id ← catalog.natural (← catalog.field input "instance_id" path) path
  unless id < count do throw s!"{path}: invalid runtime query instance {id}"
  return id

private def supported (catalog : Catalog) (input : Json) (path : String) : Except String Json := do
  catalog.requireSupported input path
  catalog.field input "value" path

def types (catalog : Catalog) (typeCount instanceCount : Nat) : Except String (Array (Option RuntimeTypeData)) := do
  let query ← catalog.field catalog.root "compiler_runtime_queries" "$"
  let rows ← catalog.array (← catalog.field query "types" "runtime queries") "runtime types"
  let mut result := Array.replicate typeCount none
  for (input,index) in rows.toList.zipIdx do
    let path := s!"runtime types[{index}]"
    environment catalog input path
    let field := fun key => catalog.field input key path
    let id ← catalog.natural (← field "input_type_id") path
    let pointer ← typeId catalog typeCount (← supported catalog (← field "mut_pointer_type") path) path
    let reference ← typeId catalog typeCount (← supported catalog (← field "mut_reference_type") path) path
    let dropGlue := do instanceId catalog instanceCount (← supported catalog (← field "drop_glue") path) path
    if bound : id < result.size then
      unless result[id].isNone do throw s!"{path}: duplicate runtime type query {id}"
      result := result.set id (some ⟨pointer,reference,dropGlue⟩) bound
    else throw s!"{path}: invalid runtime input type {id}"
  return result

def virtuals (catalog : Catalog) (typeCount instanceCount : Nat) : Decode (Array RuntimeVirtualData) := do
  let query ← catalog.field catalog.root "compiler_runtime_queries" "$"
  let rows ← catalog.array (← catalog.field query "virtual" "runtime queries") "runtime virtual queries"
  rows.mapIdxM fun index input => do
    let path := s!"runtime virtual[{index}]"
    environment catalog input path
    let field := fun key => catalog.field input key path
    let original ← catalog.natural (← field "original_instance_id") path
    unless original < instanceCount do throw s!"{path}: invalid original instance {original}"
    let method ← RegionReader.definition catalog (← field "method_definition") path
    let parent ← RegionReader.definition catalog (← field "parent_trait") path
    let concrete ← typeId catalog typeCount (← field "concrete_type") path
    let argsId ← GenericReader.arguments catalog typeCount (← field "rebased_args") path
    let state ← get
    let args ← state.arguments.lookup argsId |>.mapError (fun id => s!"{path}: invalid rebased arguments {id}")
    let resolved := do instanceId catalog instanceCount (← supported catalog (← field "resolved") path) path
    return ⟨original,method,parent,concrete,args,resolved⟩

def nativeSignatures (catalog : Catalog) (typeCount instanceCount : Nat) : Except String (Array NativeSignatureData) := do
  let rows ← catalog.array (← catalog.field catalog.root "compiler_native_signature_queries" "$") "native signatures"
  rows.mapIdxM fun index input => do
    let path := s!"native signatures[{index}]"
    let callee ← instanceId catalog instanceCount input path
    let signature := do
      let text := fun key => do catalog.string (← catalog.field input key path) path
      unless (← text "query") == "instantiate_bound_regions_with_erased(fn_sig(instance.def_id()).instantiate(instance.args))" &&
          (← text "normalization") == "none" && (← text "bound_regions") == "erased" do
        throw s!"{path}: native signature operation/region-erasure mismatch"
      let value ← supported catalog (← catalog.field input "signature_query" path) path
      let inputs ← (← catalog.array (← catalog.field value "inputs" path) path).mapM fun input => typeId catalog typeCount input path
      let output ← typeId catalog typeCount (← catalog.field value "output" path) path
      return (inputs,output)
    return ⟨callee,signature⟩

end Miri.Input.Reader.RuntimeQueryReader
