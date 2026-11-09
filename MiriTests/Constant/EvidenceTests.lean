import Miri.Interpreter.Constant
open Miri Interpreter

-- Distinct IDs represent distinct compiler instances, including their arguments.
def main : IO Unit := do
  let fnInstance : CallInstance := 8
  let otherInstance : CallInstance := 9
  let original : MIR.MirConst := .Ty 4 0
  let normalized : MIR.MirConst := .Ty 4 1
  let value : MIR.ConstValue := .Scalar (.Int 7 4)
  let entry : CompilerConstantEvidence := ⟨fnInstance, original, normalized, ⟨12⟩, value⟩
  unless (normalizationFromEvidence #[entry] fnInstance original).toOption == some normalized do
    throw (IO.userError "exact normalization query result was not reused")
  unless (evaluationFromEvidence #[entry] fnInstance normalized ⟨12⟩).toOption == some value do
    throw (IO.userError "exact evaluation query result was not reused")
  unless !(normalizationFromEvidence #[entry] otherInstance original).isOk do
    throw (IO.userError "different instance ID reused constant evidence")
  unless !(evaluationFromEvidence #[entry] fnInstance normalized ⟨13⟩).isOk do
    throw (IO.userError "different span reused constant evidence")
  unless !(evaluationFromEvidence #[entry] fnInstance original ⟨12⟩).isOk do
    throw (IO.userError "unnormalized source constant reused normalized evidence")
  unless !(normalizationFromEvidence #[entry, { entry with normalized := .Val value 4 }] fnInstance original).isOk do
    throw (IO.userError "conflicting normalization evidence was silently selected")
  unless !(evaluationFromEvidence #[entry, { entry with value := .ZeroSized }] fnInstance normalized ⟨12⟩).isOk do
    throw (IO.userError "conflicting evaluation evidence was silently selected")
  IO.println "constant compiler-evidence routing passed: constant and instance IDs retained; missing/conflicting/wrong-span evidence rejected"
