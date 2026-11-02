import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindowFalseAdvance
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindowComplete
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowFalse
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralBorrowProtectedSiblingGenerationWindow GeneralBorrowProtectedSiblingGenerationWindowCore
open GeneralBorrowFreshProtectedSlotFlags
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem seed (capacity : UInt64) (nonzero : capacity ≠ 0) (remaining : Nat) (room : remaining+2 ≤ 4294967295) :
    Unexposed (GeneralBorrowProtectedSiblingGenerationWindowCore.seed capacity nonzero remaining room).input.tree ∧
    (GeneralBorrowProtectedSiblingGenerationWindowCore.seed capacity nonzero remaining room).input.tree.nodes.size = 1 := by
  constructor
  · change Unexposed (GeneralBorrowFullSharedSeed.tree capacity nonzero BorTag.one)
    intro index node present
    have bounded := GeneralBorrowNodeUpdate.lookup_valid (GeneralBorrowFullSharedSeed.tree capacity nonzero BorTag.one).nodes index node present
    rw [GeneralBorrowFullSharedSeed.tree_eq] at bounded
    change index.toNat < 1 at bounded
    have zero : index = GeneralBorrowFullSharedSeed.root := GeneralBorrowNodeUpdate.index_injective index _ (by change index.toNat = 0;omega)
    subst index
    rw [GeneralBorrowFullSharedSeed.tree_eq] at present
    change some (GeneralBorrowFullSharedSeed.node BorTag.one) = some node at present
    cases present
    rfl
  · rfl

theorem run {capacity} (n : Nat) (before : Core capacity n) (initial : Unexposed before.input.tree) :
    ∃ after : Core capacity 0, loop capacity (List.replicate n false) (snapshot before) = .ok (snapshot after) ∧
      Unexposed after.input.tree ∧ after.input.tree.nodes.size = before.input.tree.nodes.size+n := by
  induction n with
  | zero => exact ⟨before,rfl,initial,by omega⟩
  | succ n ih =>
    obtain ⟨advance⟩ := GeneralBorrowProtectedSiblingGenerationWindowAdvance.generate before false
    have kept := GeneralBorrowProtectedSiblingGenerationWindowFalseAdvance.preserves before advance initial
    obtain ⟨after,actual,flags,count⟩ := ih advance.next kept.1
    refine ⟨after,?_,flags,by omega⟩
    rw [List.replicate_succ]
    exact (advance.actual (List.replicate n false)).trans actual

/-- From real root allocation and `n` real protected full-window constructors
with exposure selection false, all physical nodes are unexposed and the actual
node-array cardinality is exactly `n+1`. No final flag/count assumption is used. -/
theorem formed (capacity : UInt64) (nonzero : capacity ≠ 0) (n : Nat)
    (room : n+2 ≤ 4294967295) (ready : Ready capacity (List.replicate n false)) :
    Unexposed ready.input.tree ∧ ready.input.tree.nodes.size = n+1 := by
  let initial := GeneralBorrowProtectedSiblingGenerationWindowCore.seed capacity nonzero n room
  have initialFacts := seed capacity nonzero n room
  obtain ⟨after,actual,flags,count⟩ := run n initial initialFacts.1
  have operationEq : operation capacity (List.replicate n false) = .ok (snapshot after) := by
    simp only [operation,GeneralBorrowProtectedSiblingGenerationWindowSeed.root_allocation,Except.bind,bind,pure,Except.pure]
    exact actual
  have same : ready.state = snapshot after := Except.ok.inj (ready.actual.symm.trans operationEq)
  have trees : ready.input.tree = after.input.tree := ready.tree.trans (congrArg Snapshot.tree same)
  rw [trees]
  exact ⟨flags,by change after.input.tree.nodes.size = n+1;have size := initialFacts.2;change initial.input.tree.nodes.size=1 at size;omega⟩
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowFalse
