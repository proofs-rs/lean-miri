import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindowRootUniqueAdvance
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindowComplete
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowRootUnique
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralBorrowProtectedSiblingGenerationWindow GeneralBorrowProtectedSiblingGenerationWindowCore
open GeneralBorrowConstructorPriorPermission
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem seed (capacity : UInt64) (nonzero : capacity ≠ 0) (remaining : Nat) (room : remaining+2 ≤ 4294967295) :
    Every (At (GeneralBorrowProtectedSiblingGenerationWindowCore.seed capacity nonzero remaining room).input.parent (some .Unique))
      (GeneralBorrowProtectedSiblingGenerationWindowCore.seed capacity nonzero remaining room).input.tree.locations := by
  intro position valid
  change position < (GeneralBorrowFullSharedSeed.tree capacity nonzero BorTag.one).locations.entries.size at valid
  have validOne : position < 1 := by rw [GeneralBorrowFullSharedSeed.tree_eq] at valid;exact valid
  have zero : position = 0 := by omega
  subst position
  change At GeneralBorrowFullSharedSeed.root (some .Unique)
    (GeneralBorrowFullSharedSeed.tree capacity nonzero BorTag.one).locations.entries[0].data
  simp only [GeneralBorrowFullSharedSeed.tree_eq,RangeMapNonempty.homogeneous,Array.getElem_singleton]
  rfl

theorem run {capacity} (selected : List Bool) (before : Core capacity selected.length)
    (initial : Every (At before.input.parent (some .Unique)) before.input.tree.locations) :
    ∃ after : Core capacity 0,loop capacity selected (snapshot before) = .ok (snapshot after) ∧
      Every (At after.input.parent (some .Unique)) after.input.tree.locations := by
  induction selected with
  | nil => exact ⟨before,rfl,initial⟩
  | cons chosen rest ih =>
    obtain ⟨advance⟩ := GeneralBorrowProtectedSiblingGenerationWindowAdvance.generate before chosen
    have kept := GeneralBorrowProtectedSiblingGenerationWindowRootUniqueAdvance.preserves before advance initial
    obtain ⟨after,actual,unique⟩ := ih advance.next kept
    exact ⟨after,(advance.actual rest).trans actual,unique⟩

/-- The original root's stored Unique permission is formed from allocation and
retained through the actual full-window constructor/exposure history. -/
theorem formed (capacity : UInt64) (nonzero : capacity ≠ 0) (selected : List Bool)
    (room : selected.length+2 ≤ 4294967295) (ready : Ready capacity selected) :
    Every (At ready.input.parent (some .Unique)) ready.input.tree.locations := by
  let initial := GeneralBorrowProtectedSiblingGenerationWindowCore.seed capacity nonzero selected.length room
  obtain ⟨after,actual,unique⟩ := run selected initial (seed capacity nonzero selected.length room)
  have operationEq : operation capacity selected = .ok (snapshot after) := by
    simp only [operation,GeneralBorrowProtectedSiblingGenerationWindowSeed.root_allocation,Except.bind,bind,pure,Except.pure]
    exact actual
  have same : ready.state = snapshot after := Except.ok.inj (ready.actual.symm.trans operationEq)
  have trees : ready.input.tree = after.input.tree := ready.tree.trans (congrArg Snapshot.tree same)
  have parents : ready.input.parent = after.input.parent := ready.parent.trans after.parent.symm
  rw [trees,parents]
  exact unique
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowRootUnique
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowRootUnique.formed] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved generated root Unique dependency {dependency}"
