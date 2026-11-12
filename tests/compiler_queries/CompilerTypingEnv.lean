import Miri.Input.CompilerTypingEnv
open Miri.Input.CompilerTypingEnv
open Miri.Input.TraitSelection
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
def main : IO Unit := do
  check (fullyMonomorphized == ⟨⟨#[]⟩,.codegen⟩) "fully monomorphized environment differs from pinned rustc"
  let first : Clause := ⟨#[],.unstableFeature "first"⟩
  let second : Clause := ⟨#[],.unstableFeature "second"⟩
  let env : Env := ⟨⟨#[first,second,first]⟩,.codegen⟩
  let .ok (some retry) := postAnalysisRetry env | throw (IO.userError "Codegen retry missing")
  check (retry.paramEnv == env.paramEnv && retry.mode == .postAnalysis)
    "provider retry changed caller-bound order or duplicates"
  check (env != ⟨⟨#[second,first,first]⟩,.codegen⟩) "caller bounds were treated as an unordered set"
  let a : Miri.Input.GenericSubstitution.DefinitionIdentity := ⟨0,7⟩
  let b : Miri.Input.GenericSubstitution.DefinitionIdentity := ⟨0,11⟩
  check (Mode.typeck #[a,b] != .typeck #[b,a]) "local definition list order was erased"
  check (Mode.typeck #[a] != .postTypeckUntilBorrowck #[a]) "typing mode variants collided"
  check (!(postAnalysisRetry ⟨env.paramEnv,.erasedNotCoherence⟩).isOk)
    "erased typing mode entered a CTFE provider"
  check (!(deriveEmpty (.declaration a .postAnalysis)).isOk)
    "raw source declaration was accepted as a derived ParamEnv"
  IO.println "PASS exact empty Codegen, retry bounds, mode identities and source/derived environment boundary"
