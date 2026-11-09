import Miri.Input.CompilerProviders
import Miri.Interpreter.FunctionCalls

/-! helpers.rs:427–444 constructs mk_fn_sig/Binder::dummy then queries
fn_abi_of_fn_ptr with an empty extra-argument list. Match the complete source
request, never a callee ABI or a same-layout function signature. The finite
compiler catalog does not claim to answer arbitrary runtime constructors. -/
namespace Miri.Input.CompilerSignatureAbi
open Lean Miri.ABI Miri.Interpreter

def queryWithIndex (runtime : RuntimeMetadata)
    (index : CompilerQueryIndices.SignatureAbi)
    (request : FunctionCalls.SignatureRequest ABI.ExternAbi) :
    Except String (FnAbi MIR.TyId) := do
  let key := CompilerQueryIndices.signatureRequestKey request.inputs request.output
    request.abi request.safety request.cVariadic request.splatted
  let mut found : Option Nat := none
  for row in CompilerQueryIndices.signatureAbiRows index key do
    if let some previous := found then
      unless row.abiId == previous do throw "conflicting exact helper signature ABI evidence"
    found := some row.abiId
  let some abiId := found | throw s!"missing exact compiler dummy-signature ABI query: inputs={reprStr request.inputs}, output={request.output}, abi={reprStr request.abi}, safety={reprStr request.safety}, c_variadic={request.cVariadic}, splatted={request.splatted}"
  CallResolution.functionAbiId runtime abiId

def query (p : CompilerProviders.Prepared) (request : FunctionCalls.SignatureRequest ABI.ExternAbi) :
    Except String (FnAbi MIR.TyId) :=
  queryWithIndex p.runtime p.signatureAbiIndex request

def hook (p : CompilerProviders.Prepared) (_ : C) (request : FunctionCalls.SignatureRequest ABI.ExternAbi) :
    EStateM StepError S (FnAbi MIR.TyId) :=
  match query p request with
  | .ok value => pure value
  | .error reason => throw (.unsupported reason)
end Miri.Input.CompilerSignatureAbi
