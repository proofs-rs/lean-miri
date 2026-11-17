import Lean
import Miri.Interpreter.Files
namespace DuplicatePrefix.FileInitFacts
open Miri.Interpreter
open Lean Elab Tactic
elab "simp_sort_impl" : tactic => do
  let env ← getEnv
  let names ← ([".Array.qsort.sort", ".Array.qpartition.loop"] : List String).mapM fun (suffix : String) => do
    let found := env.constants.toList.filterMap fun (n,_) => if n.toString.endsWith suffix then some n else none
    let [name] := found | throwError "unique helper {suffix}"
    pure (mkIdent name)
  let names := names.toArray
  evalTactic (← `(tactic| simp [Array.qsort, Array.qpartition, $[$names:ident],*]))

theorem insert_empty (next : Nat) (reference : Files.Ref Description) :
    ({fds := #[], nextId := next} : Files.Table Description).insert reference =
      .ok (⟨#[(0, reference)], next⟩, 0) := by
  unfold Files.Table.insert Files.Table.insertWithMin
  simp_sort_impl
  rfl

theorem insert_one (next : Nat) (first reference : Files.Ref Description) :
    ({fds := #[(0, first)], nextId := next} : Files.Table Description).insert reference =
      .ok (⟨#[(0, first), (1, reference)], next⟩, 1) := by
  unfold Files.Table.insert Files.Table.insertWithMin
  simp_sort_impl
  rfl

theorem insert_two (next : Nat) (first second reference : Files.Ref Description) :
    ({fds := #[(0, first), (1, second)], nextId := next} : Files.Table Description).insert reference =
      .ok (⟨#[(0, first), (1, second), (2, reference)], next⟩, 2) := by
  unfold Files.Table.insert Files.Table.insertWithMin
  simp_sort_impl
  rfl

def initialTable (mute : Bool) : Files.Table (Files.Description Handle Directory Other) :=
  { fds := #[(0, ⟨⟨0⟩, .stdin⟩),
      (1, ⟨⟨1⟩, if mute then .nullOutput else .stdout⟩),
      (2, ⟨⟨2⟩, if mute then .nullOutput else .stderr⟩)]
    nextId := 3 }

theorem file_table_exact (mute : Bool) :
    Files.Table.init (H := Handle) (D := Directory) (O := Other) mute 64 =
      .ok (initialTable mute) := by
  cases mute <;>
    simp [Files.Table.init, Files.Table.insertNew, Files.Table.newRef,
      insert_empty, insert_one, insert_two, bind, Except.bind, pure, Except.pure,
      initialTable]

theorem file_table_exists (mute : Bool) :
    ∃ table : Files.Table (Files.Description Handle Directory Other),
      Files.Table.init mute 64 = .ok table :=
  ⟨initialTable mute, file_table_exact mute⟩

end DuplicatePrefix.FileInitFacts
