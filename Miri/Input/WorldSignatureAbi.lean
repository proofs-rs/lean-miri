import Miri.Input.WorldFunctionPointerAbi
import Miri.Interpreter.FunctionCalls

namespace Miri.Input.WorldSignatureAbi
open Miri.ABI Miri.Interpreter
/-- Pinned helpers.rs constructs an actual empty-binder FnPtr, never an Item.
No target attributes are copied into this caller-perspective query. -/
def query (request : FunctionCalls.SignatureRequest ABI.ExternAbi) :
    RuntimeArrayTypes.CompilerM (FnAbi TypeId) := do
  if request.splatted then throw "helper source request does not define a splatted argument index"
  let pointer ← RuntimeArrayTypes.liftType (TypeArena.World.internType (.functionPointer {
    abiPacked := ABI.ExternAbi.asPacked request.abi
    safe := request.safety == .Safe
    cVariadic := request.cVariadic
    splatted := none
    inputs := request.inputs
    output := request.output }))
  WorldFunctionPointerAbi.construct pointer #[]
end Miri.Input.WorldSignatureAbi
