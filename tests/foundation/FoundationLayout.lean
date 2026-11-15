import Miri.Frontend.FoundationLayout

open Lean Miri.Frontend.Foundation

-- Explicit runtime fixture, never a fallback for a foundation document.
private def target : Miri.ABI.RuntimeTargetDataLayout :=
  { Miri.ABI.RuntimeTargetDataLayout.default with i64Align := ⟨3⟩, i128Align := ⟨4⟩ }

private def expect (r : Except String FoundationLayout) (size align : Nat) : IO Unit := do
  match r with
  | .ok actual => unless actual == ⟨size, align⟩ do throw (IO.userError s!"wrong layout {repr actual}")
  | .error e => throw (IO.userError e)

private def fails (r : Except String FoundationLayout) : IO Unit := do
  match r with
  | .error _ => pure ()
  | .ok v => throw (IO.userError s!"unexpected layout {repr v}")

def main (paths : List String) : IO Unit := do
  expect (layoutOfRuntime target (.primitive "bool" "")) 1 1
  expect (layoutOfRuntime target (.primitive "char" "")) 4 4
  expect (layoutOfRuntime target (.primitive "int" "i128")) 16 16
  expect (layoutOfRuntime Miri.ABI.RuntimeTargetDataLayout.default (.primitive "int" "i64")) 8 4
  expect (layoutOfRuntime { target with i8Align := ⟨1⟩ } (.primitive "bool" "")) 1 2
  expect (layoutOfRuntime { target with i32Align := ⟨3⟩ } (.primitive "char" "")) 4 8
  expect (layoutOfRuntime { target with i16Align := ⟨2⟩ } (.array (.primitive "uint" "u16") 3)) 6 4
  expect (layoutOfRuntime { target with base := ⟨.big, .w32⟩, defaultAddressSpacePointerSpec := ⟨Miri.ABI.Size.ofBytes 4, ⟨2⟩, Miri.ABI.Size.ofBytes 4, false⟩ } (.primitive "uint" "usize")) 4 4
  expect (layoutOfRuntime target (.array (.primitive "uint" "u16") 0)) 0 2
  expect (layoutOfRuntime target (.tuple #[])) 0 1
  fails (layoutOfRuntime target (.array (.primitive "uint" "u8") (2 ^ 61)))
  fails (layoutOfRuntime target (.array (.tuple #[]) (2 ^ 64)))
  fails (layoutOfRuntime target (.tuple #[.primitive "uint" "u8"]))
  fails (layoutOfRuntime target (.primitive "float" "f32"))
  fails (layoutOfRuntime { target with i16Align := ⟨30⟩ } (.primitive "uint" "u16"))
  fails (layoutOfRuntime { target with base := ⟨.big, .w32⟩ } (.primitive "uint" "u8"))
  fails (layoutOf { triple := "missing", dataLayout := "", pointerSizeBits := 64, endian := "little" } (.primitive "uint" "u8"))
  IO.println "foundation layout: 17 self-contained checks passed"
  let fixtures ← match paths with
    | [] => pure #[]
    | [arrayPath, concretePath] => pure #[
        (arrayPath, 2, #[some (ConcreteType.primitive "uint" "u16")], #[none, some 3]),
        (concretePath, 0, #[], #[])]
    | _ => throw (IO.userError "usage: FoundationLayout.lean [ARRAY_EXPORT CONCRETE_EXPORT]")
  for (path, id, args, consts) in fixtures do
    let raw ← IO.FS.readFile path
    let d ← match Json.parse raw >>= decode with
      | .ok d => pure d
      | .error e => throw (IO.userError e)
    expect (layoutOfType d id args consts) 6 2
    fails (layoutOfType d 999 args consts)
  unless fixtures.isEmpty do
    IO.println "foundation layout: 4 fresh array/concrete export checks passed"
