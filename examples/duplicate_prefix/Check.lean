import duplicate_prefix.CurrentCallOrdinaryWitnessSafety
import duplicate_prefix.GenericFunctionPoolSafety
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAllCountSafety
import duplicate_prefix.S03EmptyContract
import duplicate_prefix.S05ZeroCellActualCallRepaired
import duplicate_prefix.Alignment
import duplicate_prefix.Borrows
import duplicate_prefix.Initial

/-! Aggregate program, component and complete-call proof roots. The checkers
run the shared transitive axiom audit after compiling their selected roots. -/

namespace DuplicatePrefix.Program

theorem pinnedTarget : imported.document.producer.targetTriple =
    "x86_64-unknown-linux-gnu" := by rfl

theorem pinnedMiri : imported.document.producer.miriCommit =
    "7fa591d7d4dd9af8154becbc8332f8096f8323b1" := by rfl

/-- Typed executable data is available for the retained document. The importer
returns this value directly after accepting the document; this presence fact
makes no semantic-coverage claim. -/
theorem structurallyReady :
    ∃ executable : Miri.Input.ExecutionInput, executable.document = imported.document :=
  ⟨imported, rfl⟩

end DuplicatePrefix.Program
