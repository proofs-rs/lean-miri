import Miri.Input.CompilerProviders
import Miri.Interpreter.FunctionCalls

/-! helpers.rs:427–444 constructs mk_fn_sig/Binder::dummy then queries
fn_abi_of_fn_ptr with an empty extra-argument list. Match the complete source
request, never a callee ABI or a same-layout function signature. Covered requests are constructed from raw session/type material; the catalog
is an exact residual for unsupported material signatures. -/
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

private def importedQuery (p : CompilerProviders.Prepared) (request : FunctionCalls.SignatureRequest ABI.ExternAbi) :
    Except String (FnAbi MIR.TyId) :=
  queryWithIndex p.runtime p.signatureAbiIndex request

/-- The caller-perspective dummy-binder signature ABI is a rustc result. Every
type key must denote the unchanged material identity in this World. -/
def queryInWorld (p : CompilerProviders.Prepared) (request : FunctionCalls.SignatureRequest ABI.ExternAbi) :
    RuntimeArrayTypes.CompilerM (FnAbi MIR.TyId) := do
  let world ← get
  for id in request.inputs.push request.output do
    let .material source ← world.arena.lookupType id
      | throw "constructed helper signature has no rustc ABI result"
    let some original := p.runtime.source.types[id]? | throw "helper material type absent"
    unless source.id == id && (← world.arena.materialKey source) == (← world.arena.materialKey original) do
      throw "helper material source differs from execution World"
  match importedQuery p request with
  | .ok abi => pure abi
  | .error error => throw error

def hook (p : CompilerProviders.Prepared) (types : RuntimeArrayQueries.Access S)
    (_ : C) (request : FunctionCalls.SignatureRequest ABI.ExternAbi) :
    EStateM StepError S (FnAbi MIR.TyId) :=
  RuntimeArrayQueries.performCompiler types (queryInWorld p request)
end Miri.Input.CompilerSignatureAbi
