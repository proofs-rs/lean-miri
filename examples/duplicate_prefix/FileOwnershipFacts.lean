import duplicate_prefix.FileInitFacts
import Miri.Interpreter.FileOwnership

set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.FileOwnershipFacts
open Miri.Interpreter

theorem register_fresh (registry : FileOwnership.Registry Description)
    (reference : Files.Ref Description)
    (fresh : ∀ entry ∈ registry.entries, entry.ref.id ≠ reference.id) :
    FileOwnership.register registry reference =
      .ok ⟨registry.entries.push ⟨reference, 1⟩⟩ := by
  have absent : registry.entries.any (·.ref.id == reference.id) = false := by
    apply Array.any_eq_false'.mpr
    intro entry member
    simpa using fresh entry member
  simp [FileOwnership.register, absent]
  rfl

theorem register_three
    (first second third : Files.Ref Description)
    (idFirst : first.id = ⟨0⟩) (idSecond : second.id = ⟨1⟩) (idThird : third.id = ⟨2⟩) :
    (do
      let registry ← FileOwnership.register {} first
      let registry ← FileOwnership.register registry second
      FileOwnership.register registry third) =
      .ok ⟨#[⟨first,1⟩, ⟨second,1⟩, ⟨third,1⟩]⟩ := by
  rw [register_fresh {} first (by simp)]
  simp only [bind, Except.bind]
  rw [register_fresh _ second (by simp [idFirst, idSecond])]
  simp only [bind, Except.bind]
  rw [register_fresh _ third (by simp [idFirst, idSecond, idThird])]
  rfl

def initialOwnership (mute : Bool) : FileOwnership.Registry (Files.Description Handle Directory Other) :=
  ⟨#[⟨⟨⟨0⟩,.stdin⟩,1⟩,
    ⟨⟨⟨1⟩, if mute then .nullOutput else .stdout⟩,1⟩,
    ⟨⟨⟨2⟩, if mute then .nullOutput else .stderr⟩,1⟩]⟩

theorem initial_ownership_loop (mute : Bool) :
    forIn (FileInitFacts.initialTable (Handle := Handle) (Directory := Directory) (Other := Other) mute).fds
        ({} : FileOwnership.Registry (Files.Description Handle Directory Other))
        (fun (entry : Int32 × Files.Ref (Files.Description Handle Directory Other)) registry => do
          let registry ← FileOwnership.register registry entry.2
          pure (.yield registry)) =
      .ok (initialOwnership mute) := by
  rw [← Array.forIn_toList]
  simp only [FileInitFacts.initialTable, Array.toList, List.forIn_cons, List.forIn_nil]
  cases mute <;> simp [FileOwnership.register, initialOwnership]
  all_goals
    split
    next h =>
      obtain ⟨i, hi, impossible⟩ := h
      have cases : i = 0 ∨ i = 1 := by omega
      rcases cases with rfl | rfl <;> simp at impossible
    next h => rfl

theorem initial_ownership_loop_match (mute : Bool) :
    forIn (FileInitFacts.initialTable (Handle := Handle) (Directory := Directory) (Other := Other) mute).fds
        ({} : FileOwnership.Registry (Files.Description Handle Directory Other))
        (fun (entry : Int32 × Files.Ref (Files.Description Handle Directory Other)) registry =>
          match FileOwnership.register registry entry.2 with
          | .error error => .error error
          | .ok registry => Except.ok (.yield registry)) =
      Except.ok (initialOwnership mute) := by
  have bodies :
      (fun (entry : Int32 × Files.Ref (Files.Description Handle Directory Other))
          (registry : FileOwnership.Registry (Files.Description Handle Directory Other)) =>
        match FileOwnership.register registry entry.2 with
        | .error error => .error error
        | .ok registry => Except.ok (.yield registry)) =
      (fun entry registry => do
        let registry ← FileOwnership.register registry entry.2
        pure (ForInStep.yield registry)) := by
    funext entry registry
    cases FileOwnership.register registry entry.2 <;> rfl
  rw [bodies]
  exact initial_ownership_loop mute

end DuplicatePrefix.FileOwnershipFacts
