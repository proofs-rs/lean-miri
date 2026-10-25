import Miri
import Miri.Frontend.ImportMIR
import Miri.Input.ExecutionChoicePolicy
import MiriTests
import Lean

/-!
Audit every imported Miri declaration, including generated/private names
whose names contain the project namespace, plus every declaration originating
in an imported MiriTests module even when its public name has no prefix.
Logical axioms supplied by Lean are
listed explicitly; unknown axioms (including sorryAx) fail elaboration.
This checks Lean dependencies, not fidelity of the Rust-to-Lean port.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for moduleName in env.header.moduleNames do
    if (`LeanMiri).isPrefixOf moduleName then
      throwError "Imported module still uses the old prefix: {moduleName}"
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    -- Private names include a module prefix; inspect their user name.
    if (`LeanMiri).isPrefixOf (privateToUserName name) then
      throwError "Declaration still uses the old namespace: {name}"
    let fromTests := (env.getModuleIdxFor? name).any fun idx =>
      (env.header.moduleNames[idx]?).any fun moduleName => (`MiriTests).isPrefixOf moduleName
    if (name.toString.splitOn "Miri").length > 1 || fromTests then
      checked := checked + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  if checked == 0 then
    throwError "Axiom audit found no Miri declarations"
  logInfo m!"Axiom audit passed for {checked} Miri declarations; allowed: propext, Quot.sound, Classical.choice"
