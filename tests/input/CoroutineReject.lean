import Miri.Input.Decoder

/-! Constructed mutations of fresh compiler evidence must fail decoding, before
MIR execution. Resource/process failures are failures of this check, not rejection
proofs. The runner must enforce its ordinary process and memory limits. -/
def main (args : List String) : IO Unit := do
  let path :: expected :: _ := args | throw (IO.userError "input and expected decoder diagnostic required")
  match Miri.Input.decodeJson (← IO.FS.readFile path) with
  | .ok _ => throw (IO.userError "malformed coroutine evidence was accepted")
  | .error error =>
    unless (error.splitOn expected).length > 1 do
      throw (IO.userError s!"wrong decoder rejection: {error}; expected {expected}")
    IO.println s!"PASS exact decoder rejection: {expected}"
