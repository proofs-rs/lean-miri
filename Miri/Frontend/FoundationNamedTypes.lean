import Miri.Frontend.FoundationPhysicalRegistry

/-! Checked declaration-path lookup and alias RHS substitution. This is not a
copied compiler named-type catalog: IDs are interned in the same source-owned
physical registry. Uncaptured OS-specific names remain unavailable. -/
namespace Miri.Frontend.Foundation
open Lean

private def sourceDefinition (document : Document) (id : Nat) (kind : String) : Except String Unit := do
  let some row := document.definitions[id]? | throw "named type source definition absent"
  unless (← row.getObjValAs? Nat "definition_id") == id &&
      (← row.getObjValAs? String "kind") == kind do throw "named type source identity/kind mismatch"

/-- Check an unambiguous crate/module/type-namespace path using only
captured module edges and alias declarations. No layout/normalization answer is
read, and a symbolic alias cannot be instantiated with missing arguments. -/
def namedAliasSource (document : Document) (path : Array String) : Except String ConcreteType := do
  unless path.size >= 2 do throw "named type source path too short"
  let some crateName := path[0]? | throw "named type source crate absent"
  let some itemName := path[path.size - 1]? | throw "named type source item absent"
  let source ← document.source.getObjVal? "named_type_source"
  let roots ← source.getObjValAs? (Array Json) "roots"
  let modules ← source.getObjValAs? (Array Json) "modules"
  let aliases ← source.getObjValAs? (Array Json) "aliases"
  let roots ← roots.filterM fun root => return (← root.getObjValAs? String "name") == crateName
  let [root] := roots.toList | throw "named type source crate absent or ambiguous"
  let rootId ← root.getObjValAs? Nat "definition"
  sourceDefinition document rootId "Mod"
  let mut parent := rootId
  for segment in path.extract 1 (path.size - 1) do
    let children ← modules.filterM fun row => do
      return (← row.getObjValAs? Nat "parent") == parent && (← row.getObjValAs? String "name") == segment
    let [child] := children.toList | throw "named type source module absent or ambiguous"
    let definition ← child.getObjValAs? Nat "definition"
    sourceDefinition document definition "Mod"
    parent := definition
  let candidates ← aliases.filterM fun row => do
    return (← row.getObjValAs? Nat "parent") == parent && (← row.getObjValAs? String "name") == itemName
  let [alias] := candidates.toList | throw "named type source alias absent or ambiguous"
  let definition ← alias.getObjValAs? Nat "definition"
  sourceDefinition document definition "TyAlias"
  unless (← alias.getObjValAs? Nat "generic_parameter_count") == 0 do
    throw "named type alias requires explicit generic arguments"
  let rhs ← (← alias.getObjVal? "rhs").getNat?
  return (← instantiate #[] #[] (← typeExpr document rhs))

/-- Exact startup keys demanded by the fixed construction path: core's C-ulong
alias and the builtin mutable i32 pointer constructor. Additional names are not
silently mapped to layout-compatible host types. -/
def startupNamedTypes (initial : PhysicalTypeRegistry) :
    Except String (PhysicalTypeRegistry × Array (String × Nat)) := do
  let ulong ← namedAliasSource initial.registry.document #["core","ffi","c_ulong"]
  let .primitive "uint" _ := ulong | throw "C-ulong source RHS is not an unsigned primitive"
  let (registry, ulongId) ← initial.intern ulong
  let (registry, pointerId) ← registry.intern (.pointer "raw_pointer_mut" (.primitive "int" "i32"))
  return (registry, #[("c_ulong",ulongId),("i32_pointer",pointerId)])

end Miri.Frontend.Foundation
