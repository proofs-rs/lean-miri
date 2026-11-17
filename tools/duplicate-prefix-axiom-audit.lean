import Lean

/-! Appended after the selected example imports by both duplicate-prefix checkers.
Audit every imported theorem and every owned declaration, including private and
generated declarations. -/

open Lean Elab Command in
run_cmd do
  let mut theorems : Nat := 0
  let mut owned : Nat := 0
  for (name, info) in (← getEnv).constants.toList do
    let theoremDecl := match info with | .thmInfo _ => true | _ => false
    let own := (name.toString.splitOn "DuplicatePrefix.").length != 1
    if theoremDecl then theorems := theorems + 1
    if own then owned := owned + 1
    if theoremDecl || own then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "{name} depends on unapproved axiom {dependency}"
  logInfo m!"PASS: audited {theorems} imported theorems and {owned} owned declarations"
