import Lean
import Miri.Input.GenericSubstitution
import Miri.ABI.PackedExternAbi

/-! Typed source FnSig material, before substitution or normalization. No
physical argument order, target classification or compiler ABI answer is read. -/
namespace Miri.Input.RawFunctionSignature
open GenericSubstitution
structure Signature where
  variables : Array BoundVariable
  inputs : Array Term
  output : Term
  abi : Miri.ABI.ExternAbi
  safety : Miri.MIR.Safety
  cVariadic : Bool
  splatted : Option Nat
  deriving Repr, DecidableEq

private def termsToArray (result : Array Term) : Terms → Array Term
  | .nil => result
  | .cons head tail => termsToArray (result.push head) tail

def read : Term → Except String Signature
  | .binder variables (.node .aggregate "signature" payload children) => do
    let header ← Lean.Json.parse payload
    for (key,_) in (← header.getObj?).toArray do
      unless ["abi_packed","safe","c_variadic","splatted"].contains key do
        throw s!"unknown raw function signature header field {key}"
    let values := termsToArray #[] children
    let some output := values.back? | throw "raw function signature has no output"
    unless values.all (fun value => value.sort == .type) do
      throw "raw function signature contains a non-type input/output"
    let abi ← Miri.ABI.ExternAbi.ofPacked (← (← header.getObjVal? "abi_packed").getNat?)
    let safety := if ← (← header.getObjVal? "safe").getBool? then
      Miri.MIR.Safety.Safe else .Unsafe
    let cVariadic ← (← header.getObjVal? "c_variadic").getBool?
    let splattedValue ← header.getObjVal? "splatted"
    let splatted ← if splattedValue == .null then pure none else some <$> splattedValue.getNat?
    pure ⟨variables,values.pop,output,abi,safety,cVariadic,splatted⟩
  | _ => .error "raw function signature requires its exact source binder and header"
end Miri.Input.RawFunctionSignature
