import Lean.Data.Json.FromToJson.Basic
import Miri.Input.CompilerTypingEnv
import Miri.Input.GenericMaterialCodec

/-! Selected-root freshness is a separate capability from the COMPLETE initial
allocation snapshot. These four typed-cache memberships are observed without
executing a query at the frozen boundary. No memo binding is inferred from
bytes, and no cached query result is seeded by this guard. -/
namespace Miri.Input.CompilerInitialCtfeFreshGuard
open Lean GenericSubstitution
set_option autoImplicit false
structure Fresh where
  private mk ::
  definition : DefinitionIdentity
private def fields (j : Json) (expected : List String) : Except String Unit := do
  let actual := (← j.getObj?).toArray.map (·.1)
  unless actual.size == expected.length && actual.all expected.contains do
    throw "selected CTFE cache guard field set differs"

def read (expected : DefinitionIdentity) (j : Json) : Except String Fresh := do
  fields j ["schema","phase","source_definition","arguments","promoted","param_env_count",
    "codegen_value_present","codegen_allocation_present","post_analysis_value_present",
    "post_analysis_allocation_present","incremental_enabled","on_disk_cache_enabled"]
  unless (← j.getObjValAs? String "schema") == "selected_ctfe_query_cache_v1" &&
      (← j.getObjValAs? String "phase") == "immediately_after_initial_freeze" do
    throw "selected CTFE cache guard schema/phase differs"
  let definitionJson ← j.getObjVal? "source_definition"
  fields definitionJson ["crate","index"]
  let definition ← GenericMaterialCodec.readDefinition definitionJson
  unless definition == expected && (← (← j.getObjVal? "arguments").getArr?).isEmpty &&
      (← j.getObjVal? "promoted") == .null && (← j.getObjValAs? Nat "param_env_count") == 0 do
    throw "selected CTFE cache guard is not this exact empty-args/empty-ParamEnv GlobalId"
  for modeFamily in ["codegen_value_present","codegen_allocation_present","post_analysis_value_present","post_analysis_allocation_present"] do
    if ← j.getObjValAs? Bool modeFamily then
      throw s!"selected CTFE root is already memoized ({modeFamily}); fresh-only source capability unavailable"
  if (← j.getObjValAs? Bool "incremental_enabled") || (← j.getObjValAs? Bool "on_disk_cache_enabled") then
    throw "selected CTFE freshness cannot exclude incremental/on-disk query restoration"
  pure ⟨definition⟩
end Miri.Input.CompilerInitialCtfeFreshGuard
