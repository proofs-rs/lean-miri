import Miri.Frontend.ImportMIR

/-! Kernel-checked facts about the imported MIR document and producer metadata.
They do not establish that every execution is safe. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open Miri.Frontend

namespace DuplicatePrefix.Program

import_mir "examples/duplicate_prefix/input.json" as imported

theorem rootedBodyCount : imported.document.bodies.size = 1 := by rfl

theorem pinnedRustc : imported.document.producer.rustcCommit =
    "8144389c895da997dbdecaa635e41d6a50be6ffd" := by rfl

end DuplicatePrefix.Program

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.Program.imported) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "Imported value depends on an unapproved axiom: {dependency}"
  for declaration in #[``DuplicatePrefix.Program.rootedBodyCount,
      ``DuplicatePrefix.Program.pinnedRustc] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on an unapproved axiom: {dependency}"
