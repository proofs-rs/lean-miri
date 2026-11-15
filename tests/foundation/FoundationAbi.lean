import Miri.Frontend.FoundationAbi

open Lean Miri.Frontend.Foundation

private def target : Target :=
  { triple := "irrelevant", dataLayout := "e-i64:64-i128:128", pointerSizeBits := 64,
    endian := "little" }

private def check (ty : ConcreteType) (expected : RustModeShape) (isReturn := false) : IO Unit := do
  match rustModeShape target "x86_64" isReturn ty with
  | .ok actual => unless actual == expected do throw (IO.userError s!"wrong shape {repr actual}")
  | .error e => throw (IO.userError e)

private def fails (result : Except String RustModeShape) : IO Unit := do
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "expected unsupported mode shape")

def main : IO Unit := do
  check (.primitive "bool" "") (.direct true)
  check (.primitive "char" "") (.direct false)
  check (.primitive "int" "i128") (.direct false) true
  check (.tuple #[]) .ignore
  check (.array (.primitive "uint" "u16") 0) .ignore
  check (.array (.primitive "uint" "u8") 3) (.integerCast 3)
  check (.array (.primitive "uint" "u8") 8) (.integerCast 8) true
  check (.array (.primitive "uint" "u8") 9) .indirect
  check (.array (.primitive "uint" "u8") 17) .indirect true
  check (.array (.array (.primitive "uint" "u16") 2) 2) (.integerCast 8)
  fails (rustModeShape target "aarch64" false (.primitive "uint" "u8"))
  fails (rustModeShape target "x86_64" false (.primitive "float" "f32"))
  fails (rustModeShape target "x86_64" false (.tuple #[.primitive "uint" "u8"]))
  let source := Json.mkObj [("compilation", Json.mkObj [
    ("panic_strategy", toJson "unwind"), ("panic_in_drop", toJson "abort")])]
  let body := Json.mkObj [("function_attributes", Json.mkObj [
    ("never_unwind", toJson false), ("is_foreign", toJson false),
    ("is_drop_glue", toJson true)])]
  match rustUnwindFactsOfSource source body with
  | .ok facts => unless !rustCanUnwind facts do throw (IO.userError "drop panic source mismatch")
  | .error e => throw (IO.userError e)
  match rustUnwindFactsOfSource Json.null body with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "accepted missing panic source facts")
  for hasDef in [false, true] do
    for never in [false, true] do
      for panic in [false, true] do
        for foreign in [false, true] do
          for dropPanic in [false, true] do
            for drop in [false, true] do
              let facts : RustUnwindFacts := ⟨hasDef, never, panic, foreign, dropPanic, drop⟩
              -- Source-order transcription, separate from the combined production predicate.
              let expected := if hasDef && never then false
                else if hasDef && !panic && !foreign then false
                else if hasDef && !dropPanic && drop then false else panic
              unless rustCanUnwind facts == expected do throw (IO.userError "unwind mismatch")
  IO.println "foundation ABI components: 13 mode checks, 2 source checks and 64 unwind checks passed"
