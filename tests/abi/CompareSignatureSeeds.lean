import Miri.Input.CompilerExternAbi
import Lean.Data.Json.Printer
import Miri.ABI.SignatureSeeds

/-! Read only signature/type/ABI categories from a fresh canonical exporter
oracle. Normalization and caller-location flags are explicit oracle dependencies;
this comparison does not test those queries or target classification. -/
open Lean Miri.Input Miri.ABI
private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
private def nat (j : Json) (key : String) : Except String Nat := do (← field j key).getNat?
private def array (j : Json) (key : String) : Except String (Array Json) := do (← field j key).getArr?
private def ids (j : Json) (key : String) : Except String (Array Nat) :=
  return ← (← array j key).mapM Json.getNat?
private def lookup (items : Array Json) (id : Nat) : Except String Json :=
  match items[id]? with
  | some value => .ok value
  | none => .error s!"oracle ID out of bounds: {id}"
private def check (j : Json) : Except String Nat := do
  unless (← nat j "schema_version") == 12 do throw "signature oracle requires canonical schema 12"
  let producer ← field j "producer"
  unless (← (← field producer "rustc_commit").getStr?) == "8144389c895da997dbdecaa635e41d6a50be6ffd" do
    throw "signature oracle rustc pin mismatch"
  let nodes ← array j "types"
  let normalize (id : Nat) : Except String Nat := do
    let node ← lookup nodes id
    unless (← nat node "type_id") == id do throw "oracle type/index mismatch"
    nat (← field (← field node "compiler_facts") "type_queries") "normalized"
  let mut tuples : Array (Nat × Array Nat) := #[]
  for node in nodes do
    let shape ← field node "shape"
    if (← (← field shape "kind").getStr?) == "tuple" then
      tuples := tuples.push (← nat node "type_id", ← (← ids shape "elements").mapM normalize)
  let tupleFields (id : Nat) := (tuples.find? (·.1 == id)).map (·.2)
  let instances ← array j "instances"
  let runtime ← field j "compiler_runtime_queries"
  let instanceFlags ← array runtime "instances"
  let abis ← array j "fn_abis"
  let arguments ← array j "abi_arguments"
  let functionTypes ← array (← field j "compiler_function_facts") "types"
  let caller ← normalize (← nat (← field j "compiler_runtime_primitives") "caller_location_type")
  let mut checked := 0
  for record in (← array j "compiler_instance_abis") do
    let instanceId ← nat record "instance_id"
    let sourceInstance ← lookup instances instanceId
    let name ← (← field sourceInstance "def_path").getStr?
    let item := (← (← field (← field sourceInstance "instance_kind") "kind").getStr?) == "item"
    if item && #["tracked", "S::prefix", "pair", "variadic"].contains name then
      let some function := functionTypes.find? (fun f =>
          ((f.getObjVal? "function_kind" >>= fun k => k.getObjVal? "instance_id") >>= Json.getNat?).toOption == some instanceId)
        | throw s!"missing source function signature {name}"
      let signature ← field function "signature_query"
      let abi ← JsonReader.run CompilerExternAbi.decode (← field signature "abi").compress
      let seed : SignatureSeed Nat := ⟨← (← ids signature "inputs").mapM normalize,
        ← normalize (← nat signature "output"), abi, ← (← field signature "c_variadic").getBool?⟩
      let some flags := instanceFlags.find? (fun f => (nat f "instance_id").toOption == some instanceId)
        | throw "missing caller-location oracle"
      let track ← (← field flags "requires_caller_location").getBool?
      let planned ← seed.plan (← (← ids record "extra_argument_types").mapM normalize)
        (if track then some caller else none) tupleFields
      let expected ← lookup abis (← nat record "abi_query")
      let actual ← (← ids expected "arguments").mapM fun id => do nat (← lookup arguments id) "type"
      let ret ← nat (← lookup arguments (← nat expected "return")) "type"
      unless planned.inputs == actual && planned.output == ret &&
          planned.fixedCount == (← nat expected "fixed_count") do
        throw s!"signature planner disagrees with rustc FnAbi for {name}: {reprStr planned.inputs} / {reprStr actual}"
      checked := checked + 1
  unless checked >= 4 do throw "fresh oracle did not exercise all four source functions"
  pure checked

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh canonical oracle JSON")
  let source ← IO.FS.readFile path
  match Json.parse source >>= check with
  | .error reason => throw (IO.userError reason)
  | .ok count => IO.println s!"Signature planner matches {count} actual pinned rustc FnAbi queries (RustCall tuple/self, caller location, C variadics)."
