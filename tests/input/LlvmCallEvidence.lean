import Miri.Input.Decoder
import Miri.Input.CompilerInstanceAbi

open Lean Miri.Input

private def must (v : Except String α) : IO α :=
  match v with | .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (e : String) : IO Unit :=
  unless b do throw (IO.userError e)
private def rejects (v : Except String α) (e : String) : IO Unit :=
  match v with | .error _ => pure () | .ok _ => throw (IO.userError e)
private def set (j : Json) (key : String) (value : Json) : Json :=
  match j.getObj? with
  | .error _ => j
  | .ok fields => Json.mkObj ((key,value) :: fields.toList.filter (·.1 != key))
private partial def mutateCalls (j : Json) (f : Json → Json) : Json :=
  match j with
  | .arr xs => .arr (xs.map (fun x => mutateCalls x f))
  | .obj fields =>
    let updated := Json.mkObj (fields.toList.map fun (key,value) => (key,mutateCalls value f))
    if j.getObjValAs? String "kind" == .ok "llvm_intrinsic" &&
        (j.getObjVal? "function_type").isOk then f updated else updated
  | _ => j

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh llvm_no_abi export")
  let text ← IO.FS.readFile path
  let raw ← must (Json.parse text)
  let decoded ← must (decodeJson text)
  let legacyText ← IO.FS.readFile "examples/empty_function/input.json"
  let _ ← must (decodeJson legacyText)
  let calls := decoded.document.bodies.flatMap (·.callEvidence.filterMap id)
  check (calls.any (·.abi == .llvmIntrinsic)) "fixture has no LLVM call evidence"
  rejects (decodeJson (set raw "schema_version" (toJson (8 : Nat))).compress)
    "schema 8 accepted new LLVM evidence"
  rejects (decodeJson (mutateCalls raw (fun j => set j "fn_abi" (toJson (0 : Nat)))).compress)
    "LLVM call accepted ordinary ABI"
  rejects (decodeJson (mutateCalls raw (fun j => set j "kind" (.str "resolved_instance"))).compress)
    "ordinary call accepted absent ABI"
  rejects (decodeJson (mutateCalls raw (fun j => set (set j "kind" (.str "resolved_instance")) "fn_abi" (toJson (0 : Nat)))).compress)
    "LLVM instance accepted normal ABI evidence"
  rejects (decodeJson (mutateCalls raw (fun j => set j "kind" (.str "indirect_function_pointer"))).compress)
    "indirect call accepted absent ABI"
  rejects (decodeJson (mutateCalls raw (fun j => set j "kind" (.str "virtual_dispatch"))).compress)
    "virtual call accepted absent ABI"
  let some item := decoded.document.instances.findIdx? (fun node =>
      match node.instanceKind with | .Item _ => true | _ => false) |
    throw (IO.userError "fixture has no Item identity")
  rejects (decodeJson (mutateCalls raw (fun j => set j "instance_id" (toJson item))).compress)
    "no-ABI evidence accepted a normal Item instance"
  rejects (decodeJson (mutateCalls raw (fun j => set j "dispatch_slot" (toJson (0 : Nat)))).compress)
    "LLVM call accepted virtual dispatch slot"
  let some llvmCall := calls.find? (·.abi == .llvmIntrinsic) |
    throw (IO.userError "missing LLVM control")
  let some llvmId := llvmCall.instanceId | throw (IO.userError "missing LLVM instance")
  let some other := calls.find? (fun call => call.abi == .llvmIntrinsic && call.instanceId != llvmCall.instanceId) |
    throw (IO.userError "fixture needs two distinct LLVM calls")
  let some otherType := other.functionType | throw (IO.userError "missing second LLVM type")
  rejects (decodeJson (mutateCalls raw (fun j => set j "function_type" (toJson otherType))).compress)
    "LLVM evidence accepted a different LLVM function type"
  let some otherId := other.instanceId | throw (IO.userError "missing second LLVM instance")
  rejects (decodeJson (mutateCalls raw (fun j => set j "instance_id" (toJson otherId))).compress)
    "LLVM evidence accepted a different LLVM instance"
  rejects (decodeJson (mutateCalls raw (fun j =>
      set (set j "function_type" (toJson otherType)) "instance_id" (toJson otherId))).compress)
    "LLVM evidence accepted a coherent foreign identity for the wrong MIR operand"
  let queries ← must (raw.getObjValAs? (Array Json) "compiler_instance_abis")
  let fake := Json.mkObj [("typing_env", .str "fully_monomorphized"),
    ("instance_id", toJson llvmId), ("extra_argument_types", .arr #[]), ("abi_query", toJson (0 : Nat))]
  rejects (decodeJson (set raw "compiler_instance_abis" (.arr (queries.push fake))).compress)
    "LLVM intrinsic accepted a fabricated ordinary ABI query"
  let some abiRow := decoded.document.queries.instanceAbis[0]? |
    throw (IO.userError "fixture has no normal ABI control")
  let forgedDocument := {decoded.document with queries := {decoded.document.queries with
    instanceAbis := decoded.document.queries.instanceAbis.push {abiRow with instanceId := llvmId}}}
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let forgedProgram ← must (lowerProgram forgedDocument)
  rejects (CompilerInstanceAbi.prepare runtime forgedProgram)
    "direct prepared API accepted a fabricated ordinary LLVM ABI row"
  let originalProgram ← must (lowerProgram decoded.document)
  let originalCalls ← must (CallResolution.prepareWithRuntime runtime originalProgram)
  check (originalCalls.entries.all (·.outcome.isOk)) "valid LLVM direct preparation failed"
  let wrongItemDocument := {decoded.document with bodies := decoded.document.bodies.map fun body =>
    {body with callEvidence := body.callEvidence.map fun evidence => evidence.map fun call =>
      if call.kind == .llvmIntrinsic then {call with instanceId := some item} else call}}
  let wrongItemProgram ← must (lowerProgram wrongItemDocument)
  let wrongItemCalls ← must (CallResolution.prepareWithRuntime runtime wrongItemProgram)
  check (wrongItemCalls.entries.any fun entry => match entry.outcome with
    | .error message => message == "LLVM call tag/canonical instance mismatch"
    | .ok _ => false) "direct call preparation accepted LLVM no-ABI tag for Item"
  IO.println "LLVM no-ABI decoder controls passed; fixed schema-8 input accepted"
