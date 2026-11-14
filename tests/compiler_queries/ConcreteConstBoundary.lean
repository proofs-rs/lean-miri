import Miri.Input.CompilerMirConstants

open Miri Miri.Input

def main : IO Unit := do
  let evaluated : MIR.ConstOperand := ⟨⟨0⟩,none,.Val .ZeroSized 0⟩
  let typeConstant : MIR.ConstOperand := ⟨⟨0⟩,none,.Ty 0 0⟩
  let unevaluated : MIR.ConstOperand := ⟨⟨0⟩,none,.Unevaluated ⟨0,#[],none⟩ 0⟩
  unless CompilerMirConstants.requireEvaluated evaluated == .ok (0,.ZeroSized) &&
      !(CompilerMirConstants.requireEvaluated typeConstant).isOk &&
      !(CompilerMirConstants.requireEvaluated unevaluated).isOk do
    throw (IO.userError "runtime constant boundary accepted an unevaluated source")
  IO.println "PASS rustc evaluated MIR constant boundary"
