import Miri.Input.Reader.Catalog
import Miri.Input.CompilerTables

namespace Miri.Input.Reader
open Lean

private def typeReference (catalog : Catalog) (input : Json) (path : String) : Except String TypeId := do
  catalog.natural (← catalog.field input "type_id" path) (path ++ ".type_id")

private def supportedReference (catalog : Catalog) (kind : String) (input : Json) (path : String) : Except String TypeId := do
  unless (← catalog.string (← catalog.field input "status" path) path) == "supported" do
    let reason := do catalog.string (← catalog.field input "reason" path) path
    throw s!"compiler {kind} query unavailable: {reason.toOption}"
  typeReference catalog (← catalog.field input "value" path) (path ++ ".value")

private def typeCatalog (catalog : Catalog) (input : Except String Json) (path : String)
    (decode : Json → String → Except String TypeId) : Except String (Array (String × Except String TypeId)) := do
  let .obj entries ← catalog.inspect (← input) path | throw s!"{path}: expected type catalog object"
  return entries.toList.toArray.map fun (key,value) => (key,decode value s!"{path}.{key}")

private def canonicalEntries (catalog : Catalog) (field kind : String)
    (cratePath : Array String) : Except String Json := do
  let value ← catalog.field catalog.root field "$"
  let path := "$." ++ field
  let crate ← catalog.array (← catalog.field value "crate_path" path) path
  let crate ← crate.mapM fun part => catalog.string part path
  unless crate == cratePath do throw s!"compiler {kind} type query has wrong canonical crate path"
  unless (← catalog.string (← catalog.field value "namespace" path) path) == "TypeNS" do
    throw s!"compiler {kind} type query has wrong namespace"
  unless (← catalog.string (← catalog.field value "typing_env" path) path) == "fully_monomorphized" do
    throw s!"compiler {kind} type query has wrong typing environment"
  catalog.field value "entries" path

def Catalog.readPrimitiveTypes (catalog : Catalog) : CompilerTypeCatalogs := Id.run do
  let primitives := catalog.field catalog.root "compiler_runtime_primitives" "$"
  let named := catalog.field catalog.root "compiler_named_types" "$"
  let libc := canonicalEntries catalog "compiler_libc_type_layouts" "libc" #["libc"]
  let windows := canonicalEntries catalog "compiler_windows_type_layouts" "Windows" #["std","sys","pal","windows","c"]
  return {
    primitives := typeCatalog catalog primitives "$.compiler_runtime_primitives" (typeReference catalog)
    primitiveQueries := typeCatalog catalog primitives "$.compiler_runtime_primitives" (supportedReference catalog "type")
    named := typeCatalog catalog named "$.compiler_named_types" (supportedReference catalog "type")
    libc := typeCatalog catalog libc "$.compiler_libc_type_layouts.entries" (supportedReference catalog "libc type/layout")
    windows := typeCatalog catalog windows "$.compiler_windows_type_layouts.entries" (supportedReference catalog "Windows type/layout") }
end Miri.Input.Reader
