import Miri.Frontend.FoundationSession

open Lean Miri.Frontend.Foundation

private def fixture (session : Json) : Document := {
  source := Json.mkObj [("session", session)]
  target := { triple := "x86_64-unknown-linux-gnu", architecture := "x86_64", dataLayout := "", pointerSizeBits := 64, endian := "little" }
  definitions := #[], types := #[], bodies := #[] }

private def material (debug : Bool) (ub contract overflow : Option Bool) : Json :=
  Json.mkObj [("internal_target_features", toJson (#["sse2"] : Array String)),
    ("is_like_wasm", toJson false), ("target_arch", toJson "x86_64"),
    ("debug_assertions", toJson debug), ("ub_checks", toJson ub),
    ("contract_checks", toJson contract), ("overflow_checks", toJson overflow)]

def main : IO Unit := do
  for debug in [false, true] do
    for ub in [none, some false, some true] do
      for contract in [none, some false, some true] do
        for overflow in [none, some false, some true] do
          let session ← IO.ofExcept (sessionOfDocument (fixture (material debug ub contract overflow)) 7)
          unless session.rootSpan == 7 && session.targetArch == "x86_64" &&
              session.runtimeChecks == #[
                (.UbChecks, ub.getD debug), (.ContractChecks, contract.getD false),
                (.OverflowChecks, overflow.getD debug)] do
            throw (IO.userError "incorrect session computation")
  for invalid in [Json.null, Json.mkObj [],
      material true none none none |>.setObjVal! "target_arch" (toJson "wasm32"),
      material true none none none |>.setObjVal! "ub_checks" (toJson "true"),
      material true none none none |>.setObjVal! "internal_target_features" (toJson (#["sse2", "sse2"] : Array String))] do
    match sessionInputs (fixture invalid) with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "invalid session accepted")
  IO.println "foundation session: 54 option combinations and 5 rejection checks passed"
