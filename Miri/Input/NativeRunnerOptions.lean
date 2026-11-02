namespace Miri.NativeRunnerOptions

/-- Remove the optional diagnostic bound without changing the order of the
remaining source/profile arguments. Ordinary runs have no iteration bound. -/
def iterationLimit : List String → Except String (List String × Option Nat)
  | [] => .ok ([], none)
  | "--max-iterations" :: [] => .error "--max-iterations requires an unsigned integer"
  | "--max-iterations" :: raw :: rest => do
      let some count := raw.toNat? | throw "--max-iterations requires an unsigned integer"
      let (args, existing) ← iterationLimit rest
      unless existing.isNone do throw "duplicate --max-iterations"
      return (args, some count)
  | arg :: rest => do
      let (args, count) ← iterationLimit rest
      return (arg :: args, count)

end Miri.NativeRunnerOptions
