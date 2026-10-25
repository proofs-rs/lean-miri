import Miri.Interpreter.Constant
open Miri Interpreter

-- Synthetic exact-key/cache tests. These records test query routing, not the
-- correctness of a rustc normalization/evaluation result supplied by a client.
def main : IO Unit := do
  let fnInstance : CallInstance := ⟨.Item 8, #[.Const 2]⟩
  let wrongArgs : CallInstance := ⟨.Item 8, #[.Const 3]⟩
  let original : MIR.MirConst := .Ty 4 (.Param 0 "N" none)
  let normalized : MIR.MirConst := .Ty 4 (.Value 4 ⟨#[.Leaf 7 4], 0⟩)
  let value : MIR.ConstValue := .Scalar (.Int 7 4)
  let entry : CompilerConstantEvidence := ⟨fnInstance, original, normalized, ⟨12⟩, value⟩
  unless (normalizationFromEvidence #[entry] fnInstance original).toOption == some normalized do
    throw (IO.userError "exact normalization query result was not reused")
  unless (evaluationFromEvidence #[entry] fnInstance normalized ⟨12⟩).toOption == some value do
    throw (IO.userError "exact evaluation query result was not reused")
  unless !(normalizationFromEvidence #[entry] wrongArgs original).isOk do
    throw (IO.userError "different InstanceArgs reused constant evidence")
  unless !(evaluationFromEvidence #[entry] fnInstance normalized ⟨13⟩).isOk do
    throw (IO.userError "different span reused constant evidence")
  unless !(evaluationFromEvidence #[entry] fnInstance original ⟨12⟩).isOk do
    throw (IO.userError "unnormalized source constant reused normalized evidence")
  unless !(normalizationFromEvidence #[entry, { entry with normalized := .Val value 4 }] fnInstance original).isOk do
    throw (IO.userError "conflicting normalization evidence was silently selected")
  unless !(evaluationFromEvidence #[entry, { entry with value := .ZeroSized }] fnInstance normalized ⟨12⟩).isOk do
    throw (IO.userError "conflicting evaluation evidence was silently selected")
  IO.println "constant compiler-evidence routing passed: original form and InstanceArgs retained; missing/conflicting/wrong-span evidence rejected"
