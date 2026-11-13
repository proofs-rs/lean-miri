import Lean.Data.Json.FromToJson.Basic
import Miri.Input.CompilerInitialAllocationSymbols
import Miri.Input.CtfeQueryBridge

/-! A bounded selected cache table, never a complete query-system snapshot.
Every one of the four explicit slots is retained or rejects the whole input;
no presence, result or allocation identity is inferred from heap contents. -/
namespace Miri.Input.CompilerInitialSelectedMemo
open Lean GenericSubstitution
set_option autoImplicit false
inductive RawAnswer where
  | value (bits : UInt32) (sourceType : Json)
  | allocation (sourceId : UInt64) (sourceType : Json)
structure RawSlot where
  family : CtfeQueryBridge.Family
  mode : CompilerTypingEnv.Mode
  answer : Option RawAnswer
structure Raw where
  definition : DefinitionIdentity
  definitionKind : String
  sourceType : Json
  slots : Array RawSlot

def exactFields (j : Json) (expected : List String) : Except String Unit := do
  let fields := (← j.getObj?).toArray.map (·.1)
  unless fields.size == expected.length && fields.all expected.contains do
    throw "selected initial memo field set differs"
private def definition (j : Json) : Except String DefinitionIdentity := do
  exactFields j ["crate","index"]
  GenericMaterialCodec.readDefinition j
private def unsigned (j : Json) : Except String UInt64 := do
  let n ← j.getNat?
  unless n < 2^64 do throw "selected memo source AllocId exceeds u64"
  pure (UInt64.ofNat n)
private def readAnswer (family : CtfeQueryBridge.Family) (j : Json) : Except String RawAnswer := do
  unless (← j.getObjValAs? String "kind") == "ok" do
    throw "selected initial memo cached diagnostic/TooGeneric result unsupported"
  match family with
  | .value =>
    exactFields j ["kind","value","source_type"]
    let value ← j.getObjVal? "value"
    exactFields value ["kind","bits_unsigned","size_bytes"]
    unless (← value.getObjValAs? String "kind") == "scalar_int" &&
        (← value.getObjValAs? Nat "size_bytes") == 4 do
      throw "selected initial memo requires u32 ScalarInt, not another ConstValue"
    let text ← value.getObjValAs? String "bits_unsigned"
    let some n := text.toNat? | throw "selected initial memo scalar is not unsigned decimal"
    unless n < 2^32 && toString n == text do throw "selected initial memo scalar exceeds exact u32 representation"
    pure (.value (UInt32.ofNat n) (← j.getObjVal? "source_type"))
  | .allocation =>
    exactFields j ["kind","allocation"]
    let value ← j.getObjVal? "allocation"
    exactFields value ["source_alloc_id","source_type"]
    let sourceId ← unsigned (← value.getObjVal? "source_alloc_id")
    unless sourceId != 0 do throw "selected initial memo ConstAlloc source ID is zero"
    pure (.allocation sourceId (← value.getObjVal? "source_type"))
  | .staticInitializer => throw "selected initial memo does not admit static initializer queries"
private def readSlot (owner : DefinitionIdentity) (j : Json) : Except String RawSlot := do
  exactFields j ["key","present","result"]
  let key ← j.getObjVal? "key"
  exactFields key ["family","typing_env","instance","promoted"]
  let family ← match ← key.getObjValAs? String "family" with
    | "value" => pure CtfeQueryBridge.Family.value
    | "allocation" => pure .allocation
    | _ => throw "selected initial memo family unsupported"
  let environment ← key.getObjVal? "typing_env"
  exactFields environment ["mode","param_env"]
  let mode ← match ← environment.getObjValAs? String "mode" with
    | "codegen" => pure CompilerTypingEnv.Mode.codegen
    | "post_analysis" => pure .postAnalysis
    | _ => throw "selected initial memo typing mode unsupported"
  unless (← (← environment.getObjVal? "param_env").getArr?).isEmpty &&
      (← key.getObjVal? "promoted") == .null do throw "selected initial memo nonempty bounds/promoted unsupported"
  let callee ← key.getObjVal? "instance"
  exactFields callee ["kind","arguments"]
  let kind ← callee.getObjVal? "kind"
  exactFields kind ["kind","definition"]
  unless (← kind.getObjValAs? String "kind") == "item" &&
      (← definition (← kind.getObjVal? "definition")) == owner &&
      (← (← callee.getObjVal? "arguments").getArr?).isEmpty do
    throw "selected initial memo key is not this exact empty-argument physical Item"
  let present ← j.getObjValAs? Bool "present"
  let result ← j.getObjVal? "result"
  if present then pure ⟨family,mode,some (← readAnswer family result)⟩
  else
    unless result == .null do throw "absent selected memo slot contains a result"
    pure ⟨family,mode,none⟩
private def flagName (slot : RawSlot) : String :=
  (if slot.mode == .codegen then "codegen" else "post_analysis") ++
    (if slot.family == .value then "_value_present" else "_allocation_present")
def decode (j : Json) : Except String Raw := do
  exactFields j ["schema","phase","result_scope","source_definition","source_definition_kind","source_type","membership","slots"]
  unless (← j.getObjValAs? String "schema") == "selected_const_initial_query_cache_v1" &&
      (← j.getObjValAs? String "phase") == "before_export_queries" &&
      (← j.getObjValAs? String "result_scope") == "selected_u32_success_v1" do
    throw "selected initial memo schema/phase/scope differs"
  let owner ← definition (← j.getObjVal? "source_definition")
  let kind ← j.getObjValAs? String "source_definition_kind"
  unless kind == "const" || kind == "associated_const" do throw "selected initial memo requires Const/AssocConst owner"
  let membership ← j.getObjVal? "membership"
  exactFields membership ["schema","phase","source_definition","arguments","promoted","param_env_count","codegen_value_present","codegen_allocation_present","post_analysis_value_present","post_analysis_allocation_present","incremental_enabled","on_disk_cache_enabled"]
  unless (← membership.getObjValAs? String "schema") == "selected_ctfe_query_cache_v1" &&
      (← membership.getObjValAs? String "phase") == "immediately_after_initial_freeze" &&
      (← definition (← membership.getObjVal? "source_definition")) == owner &&
      (← (← membership.getObjVal? "arguments").getArr?).isEmpty &&
      (← membership.getObjVal? "promoted") == .null &&
      (← membership.getObjValAs? Nat "param_env_count") == 0 do
    throw "selected memo membership key/phase differs"
  if (← membership.getObjValAs? Bool "incremental_enabled") ||
      (← membership.getObjValAs? Bool "on_disk_cache_enabled") then
    throw "selected memo incremental/on-disk restoration unsupported"
  let rows ← (← j.getObjVal? "slots").getArr?
  unless rows.size == 4 do throw "selected memo must contain exactly four explicit slots"
  let slots ← rows.mapM (readSlot owner)
  let mut seen : Array (CtfeQueryBridge.Family × CompilerTypingEnv.Mode) := #[]
  for slot in slots do
    let key := (slot.family,slot.mode)
    if seen.contains key then throw "selected memo repeats a family/mode key"
    seen := seen.push key
    unless (← membership.getObjValAs? Bool (flagName slot)) == slot.answer.isSome do
      throw "selected memo slot presence differs from captured membership"
  pure ⟨owner,kind,← j.getObjVal? "source_type",slots⟩
end Miri.Input.CompilerInitialSelectedMemo
