import Miri.ABI.PackedExternAbi
import Miri.Input.GenericSubstitution
import Miri.Input.RawFunctionSignature
import Lean

/-! Pinned pretty.rs FnSig / pretty_print_fn_sig source branches. This module
prints a supplied instantiated source signature; it never selects a signature
or uses another instantiation's display. -/
namespace Miri.Input.FunctionTypePrinter
open GenericSubstitution
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
  let inner ← lift (body 16 signature)
  let source ← lift (RawFunctionSignature.read (.binder #[] inner))
  let abi := source.abi
  let safe := source.safety == .Safe
  let variadic := source.cVariadic
  let splatted := source.splatted
  let inputs := source.inputs
  let output := source.output
  let mut result ← emit (if safe || forceSafe then "" else "unsafe ")
  if abi != .Rust then
    result := result ++ (← emit ("extern \"" ++ Miri.ABI.ExternAbi.asStr abi ++ "\" "))
  result := result ++ (← emit "fn(")
  for index in [:inputs.size] do
    if index > 0 then result := result ++ (← emit ", ")
    if splatted == some index then result := result ++ (← emit "#[rustc_splat] ")
    let some input := inputs[index]? | throw "function signature input absent"
    result := result ++ (← printType input)
  if variadic then
    if !inputs.isEmpty then result := result ++ (← emit ", ")
    result := result ++ (← emit "...")
  result := result ++ (← emit ")")
  unless output == .node .type "tuple" "" .nil do
    result := result ++ (← emit " -> ") ++ (← printType output)
  pure result
end Miri.Input.FunctionTypePrinter
