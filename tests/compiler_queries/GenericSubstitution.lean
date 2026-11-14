import Miri.Input.GenericSubstitution

open Miri.Input.GenericSubstitution

private def parameter : Term := .parameter .type 0
private def region (depth : Nat) : Term := .bound .region (.Bound depth) 0 (.namedForPrinting "a")
private def reference (lifetime : Term) : Term :=
  .node .type "reference" "immutable" #[lifetime, .atom .type "u32" ""]
private def function (argument : Term) : Term :=
  .node .type "fn_ptr" "Rust" #[Term.binder #[] (.node .aggregate "signature" "" #[argument])]

private def matchesResult (result : Except String Term) (expected : Term) : Bool :=
  match result with | .ok value => value == expected | .error _ => false

def main : IO Unit := do
  unless matchesResult (instantiate 20 #[reference (region 0)] (function parameter))
      (function (reference (region 1))) do
    throw (IO.userError "escaping substitution region was captured")
  -- Entering a binder inside the replacement protects its local variables.
  unless matchesResult (shift 20 2 0 (function (reference (region 0))))
      (function (reference (region 0))) do
    throw (IO.userError "local replacement region was shifted")
  unless matchesResult (shift 20 2 0 (function (reference (region 1))))
      (function (reference (region 3))) do
    throw (IO.userError "escaping replacement region was not shifted")

example : shift 20 2 0 (.bound .type .Canonical 0 (.namedForPrinting "T")) =
    .ok (.bound .type .Canonical 0 (.namedForPrinting "T")) := by rfl
example : instantiate 20 #[.placeholder .type 1 3 (.namedForPrinting "T")] parameter =
    .ok (.placeholder .type 1 3 (.namedForPrinting "T")) := by rfl
example : instantiate 20 #[.atom .constant "value" "3"] parameter =
    .error "generic parameter argument sort mismatch" := by rfl
example : instantiate 20 #[] parameter =
    .error "generic material has parameters but no arguments" := by rfl
-- Empty args skip all folding; nonempty args directly folding a ReVar fail.
example : instantiate 20 #[] (.inference .region 3) = .ok (.inference .region 3) := by rfl
example : instantiate 20 #[.atom .type "u32" ""] (.inference .region 3) =
    .error "unexpected inference region in generic substitution" := by rfl
