import Miri.Input.CompilerProviders
import Miri.Interpreter.FunctionCalls

namespace Miri.Input.CompilerSignatureAbi
open Lean Miri.ABI Miri.Interpreter

def query (p : CompilerProviders.Prepared) (request : FunctionCalls.SignatureRequest ABI.ExternAbi) :
    Except String (FnAbi MIR.TyId) := do
  if request.splatted then throw "helper signature must be unsplatted"
  let context : CompilerFacts.Context := ⟨p.runtime, p.program, p.lowering⟩
  let signature : FunctionSignature := {
    inputs := request.inputs, output := request.output, safety := request.safety
    abi := request.abi, cVariadic := request.cVariadic }
  SourceAbiRuntime.ofSignature context.runtime signature

def hook (p : CompilerProviders.Prepared) (_ : C) (request : FunctionCalls.SignatureRequest ABI.ExternAbi) :
    EStateM StepError S (FnAbi MIR.TyId) :=
  match query p request with
  | .ok value => pure value
  | .error reason => throw (.unsupported reason)
end Miri.Input.CompilerSignatureAbi
