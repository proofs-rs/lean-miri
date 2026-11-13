import Miri.Input.CompilerInitialSelectedMemoProvider
import Miri.Input.ProfileDocument
import Miri.Input.CompilerInitialAllocationPreparation
import Miri.Input.EvalPreparation
import Miri.Input.CompilerInitialCtfeRootSource

/-! Allocation profiles are explicit alternatives. The initial profile retains
its complete typed store and extended type arena alongside the common runtime
preparation; its final exporter graph is never imported into the initial heap. -/
namespace Miri.Input.ProfilePreparation
open Lean Miri.Memory Miri.Interpreter
set_option autoImplicit false

inductive Prepared where
  | legacy (prepared : EvalPreparation.Prepared)
  | initial (prepared : CompilerInitialAllocationPreparation.Prepared) (ctfeRoots : Array CompilerInitialCtfeRootSource.Prepared) (selected : CompilerInitialSelectedMemo.Registry)

structure Attempt where
  memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
  outcome : Except String Prepared

def Prepared.base : Prepared → EvalPreparation.Prepared
  | .legacy prepared => prepared
  | .initial prepared _ _ =>
    ⟨prepared.compiler,prepared.image,prepared.types,prepared.layouts,prepared.dummySpan⟩

private def prepareLoweredProfiled (profile : Options) (budget run : Nat)
    (decoded : ProfileDocument.Decoded) (program : LoweredProgram) : Attempt :=
  match decoded with
  | .legacy _ =>
    let attempt := EvalPreparation.prepareProfiled profile program
    ⟨attempt.memory,attempt.outcome.map .legacy⟩
  | .initial source =>
    let attempt := CompilerInitialAllocationPreparation.prepareProfiled profile budget run source.snapshot program
    match attempt.outcome with
    | .error error => ⟨attempt.memory,.error error⟩
    | .ok prepared => Id.run do
      let some (_,initialNext) := prepared.initialWorld.runs.find? (fun row => row.1 == run)
        | return ⟨attempt.memory,.error "initial allocation run absent after installation"⟩
      let initialDedup := (prepared.initialWorld.typedDedup.filter (fun row => row.run == run)).size
      let (selected,selectedTypes) ← match CompilerInitialSelectedMemo.importTables prepared.compiler.runtime
          prepared.snapshot run source.selectedCache prepared.types {prepared.initialWorld with memory := attempt.memory} with
        | .error error => return ⟨attempt.memory,.error error⟩
        | .ok value => pure value
      let mut types := selectedTypes
      let mut roots : Array CompilerInitialCtfeRootSource.Prepared := #[]
      for row in source.ctfeRoots do
        match CompilerInitialCtfeRootSource.prepare source.originalDocument initialNext initialDedup row types with
        | .error error => return ⟨attempt.memory,.error error⟩
        | .ok root =>
          if roots.any (fun previous => decide (previous.query = root.query)) then
            return ⟨attempt.memory,.error "duplicate selected CTFE query key"⟩
          types := root.types
          roots := roots.push root
      return ⟨attempt.memory,.ok (.initial {prepared with types} roots selected)⟩

/-- Lower only the document selected by the profile dispatcher. A caller cannot
pair a snapshot/roots descriptor with an independently supplied program. -/
def prepareProfiled (profile : Options) (budget run : Nat)
    (decoded : ProfileDocument.Decoded) : Attempt :=
  match lowerProgram decoded.input.document with
  | .error error => ⟨.empty,.error error⟩
  | .ok program => prepareLoweredProfiled profile budget run decoded program

end Miri.Input.ProfilePreparation
