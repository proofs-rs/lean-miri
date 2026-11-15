import Miri.Frontend.FoundationPrimitiveFacts

open Lean Miri.Frontend.Foundation

private def expect (r : Except String α) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  for ty in #[ConcreteType.primitive "bool" "", .primitive "char" "",
      .primitive "int" "isize", .array (.array (.primitive "uint" "u8") 0) 9,
      .tuple #[]] do
    let facts ← expect (primitiveCompilerFacts ty 11 12 13)
    check (facts.booleanQueries.find? (·.1 == "is_freeze") == some ("is_freeze", true)) "freeze"
    check (facts.booleanQueries.find? (·.1 == "needs_drop") == some ("needs_drop", false)) "drop"
    check (facts.typeQueries.find? (·.1 == "normalized") == some ("normalized", some 11)) "self"
    check (facts.typeIdHash.isNone) "invented type hash"
    check ((facts.booleanQueries.find? (·.1 == "unknown")).isNone) "unknown became false"
  for ty in #[ConcreteType.primitive "float" "f32", .primitive "uint" "i8",
      .tuple #[.primitive "bool" ""], .array (.primitive "float" "f64") 0] do
    match primitiveCompilerFacts ty 0 1 2 with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "unsupported facts accepted")
  match args with
  | [] => pure ()
  | [path] =>
    let document ← expect (Json.parse (← IO.FS.readFile path) >>= decode)
    let (initial, id) ← expect ((PhysicalTypeRegistry.start document).intern
      (.array (.primitive "uint" "u8") 4))
    let ready ← expect initial.withPrimitiveFacts
    check (ready.types.size == initial.types.size + 1) "unit/u8 closure"
    let (node, _) ← expect (ready.lookup id)
    let some facts := node.compilerFacts | throw (IO.userError "missing derived facts")
    check (facts.typeQueries.find? (·.1 == "normalized") == some ("normalized", some id)) "registry identity"
    let again ← expect ready.withPrimitiveFacts
    check (again.types.size == ready.types.size) "closure not idempotent"
  | _ => throw (IO.userError "usage: FoundationPrimitiveFacts [FOUNDATION_JSON]")
  IO.println "foundation primitive facts: structural answers, failures and identity closure passed"
