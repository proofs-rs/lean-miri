import Miri.ABI.PackedExternAbi
import Miri.Input.GenericSubstitution
import Lean

/-! Pinned pretty.rs FnSig / pretty_print_fn_sig source branches. This module
prints a supplied instantiated source signature; it never selects a signature
or uses another instantiation's display. -/
namespace Miri.Input.FunctionTypePrinter
open GenericSubstitution
private def collect (result : Array Term) : Terms → Array Term
  | .nil => result | .cons head tail => collect (result.push head) tail
private def body : Nat → Term → Except String Term
  | 0, _ => throw "function signature binder recursion exhausted"
  | fuel+1, .binder variables inner =>
    if variables.isEmpty then body fuel inner
    else throw "function signature bound-variable naming is not implemented"
  | _, term => pure term
private def lift [Monad m] [MonadExceptOf String m] (value : Except String A) : m A :=
  match value with | .ok value => pure value | .error error => throw error

def render [Monad m] [MonadExceptOf String m]
    (emit : String → m String) (printType : Term → m String) (signature : Term) (forceSafe : Bool := false) : m String := do
  let .node .aggregate "signature" payload children ← lift (body 16 signature)
    | throw "function printer requires raw signature expression"
  let header ← lift (Lean.Json.parse payload)
  for (key,_) in (← lift header.getObj?).toArray do
    unless ["abi_packed", "safe", "c_variadic", "splatted"].contains key do
      throw "function printer signature header has unknown field"
  let abi ← lift ((← lift (header.getObjVal? "abi_packed")).getNat?)
  let abi ← lift (Miri.ABI.ExternAbi.ofPacked abi)
  let safe ← lift ((← lift (header.getObjVal? "safe")).getBool?)
  let variadic ← lift ((← lift (header.getObjVal? "c_variadic")).getBool?)
  let splattedValue ← lift (header.getObjVal? "splatted")
  let splatted ← if splattedValue == .null then pure none
    else some <$> lift splattedValue.getNat?
  let children := collect #[] children
  let some output := children.back? | throw "function signature output absent"
  let inputs := children.pop
  let mut result ← emit (if safe || forceSafe then "" else "unsafe ")
  if abi != .Rust then
    result := result ++ (← emit ("extern \"" ++ Miri.ABI.ExternAbi.asStr abi ++ "\" "))
  result := result ++ (← emit "fn(")
  for index in [:inputs.size] do
    if index > 0 then result := result ++ (← emit ", ")
    if splatted == some index then result := result ++ (← emit "#[rustc_splat] ")
    let some input := inputs[index]? | throw "function signature input absent"
    result := result ++ (← printType input)
  if let some index := splatted then
    if index >= inputs.size then
      if index > 0 then result := result ++ (← emit ", ")
      result := result ++ (← emit "#[rustc_splat] ")
  if variadic then
    if !inputs.isEmpty then result := result ++ (← emit ", ")
    result := result ++ (← emit "...")
  result := result ++ (← emit ")")
  unless output == .node .type "tuple" "" .nil do
    result := result ++ (← emit " -> ") ++ (← printType output)
  pure result
end Miri.Input.FunctionTypePrinter
