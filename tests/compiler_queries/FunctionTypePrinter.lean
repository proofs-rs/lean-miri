import Miri.Input.FunctionTypePrinter
open Miri.Input GenericSubstitution
private def render (safe variadic : Bool) (abi : Nat) (splatted : Option Nat) (inputs : Array Term) (output : Term) : Option String :=
  let payload := Lean.Json.compress (Lean.Json.mkObj [("abi_packed",Lean.toJson abi),("safe",Lean.toJson safe),
    ("c_variadic",Lean.toJson variadic),("splatted",Lean.toJson splatted)])
  match FunctionTypePrinter.render (m := Except String) pure
      (fun term => match term with | .atom .type "bool" _ => pure "bool" | .atom .type "never" _ => pure "!" | _ => throw "unsupported test term")
      (.binder #[] (.node .aggregate "signature" payload (Terms.ofArray (inputs.push output)))) with
  | .ok result => some result | .error _ => none
private def b : Term := .atom .type "bool" ""
private def n : Term := .atom .type "never" ""
private def unit : Term := .node .type "tuple" "" .nil
def main : IO Unit := do
  unless render true false 2 none #[b] n == some "fn(bool) -> !" do throw (IO.userError "safe signature differs")
  unless render false false 2 none #[] unit == some "unsafe fn()" do throw (IO.userError "unsafe unit signature differs")
  unless render true true 2 none #[b] unit == some "fn(bool, ...)" do throw (IO.userError "variadic signature differs")
  unless render true false 2 (some 0) #[b] unit == some "fn(#[rustc_splat] bool)" do throw (IO.userError "splatted signature differs")
  unless render true false 0 none #[b] unit == none do throw (IO.userError "unsupported ABI unexpectedly printed")
  IO.println "PASS five source-signature printer runtime controls (not kernel proofs)"
