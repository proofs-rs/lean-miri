import duplicate_prefix.GeneralBorrowExposedKnownRootWriteLoop

namespace DuplicatePrefix.GeneralBorrowExposedKnownRootWriteFold
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootWriteState
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]

set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Actual source-order virtual-root calls recur on the original raw coherent
counter data. Write counters and protected readability are carried through each
nonleaf source DFS; changed Write counters need no success hypothesis. -/
theorem run_from (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (roots : List UniIndex) (maximum : Option Miri.Memory.BorTag) (weights : Weights tree)
    (bound : ∀ root ∈ roots, weights.weight root ≤ tree.nodes.size)
    (data : ∀ root ∈ roots, Data tree initial root protections)
    (frame : WriteFrame initial current) (profile : Profile tree current protections)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections) (noCutoff : ∀ index node, area.support index → tree.nodes.get index = some node →
      GeneralBorrowWildcardVirtualLeaf.onlyForeign node maximum = false) :
    ∃ after, GeneralBorrowWildcardVirtualLeafFold.run tree roots current maximum .Write protections = ⟨after,.Completed⟩ ∧
      WriteFrame initial after ∧ Profile tree after protections ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections := by
  induction roots generalizing current with
  | nil => exact ⟨current,rfl,frame,profile,coherent⟩
  | cons root rest ih =>
    have first := GeneralBorrowExposedKnownRootWriteLoop.access_from tree initial root maximum protections weights
      (bound root (by simp)) (data root (by simp)) current frame profile coherent noCutoff
    let called := tree.performWildcardAccessAt current root maximum .Write protections true
    obtain ⟨after,tail,afterFrame,afterProfile,afterCoherent⟩ := ih called.location (fun root member => bound root (by simp [member]))
      (fun root member => data root (by simp [member])) first.2.1 first.2.2.1 first.2.2.2
    refine ⟨after,?_,afterFrame,afterProfile,afterCoherent⟩
    have status : (tree.performWildcardAccessAt current root maximum .Write protections true).status = .Completed := first.1
    simpa only [GeneralBorrowWildcardVirtualLeafFold.run,status,beq_self_eq_true,ite_true] using tail

theorem run (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (roots : List UniIndex) (maximum : Option Miri.Memory.BorTag) (weights : Weights tree)
    (bound : ∀ root ∈ roots, weights.weight root ≤ tree.nodes.size)
    (data : ∀ root ∈ roots, Data tree initial root protections)
    (profile : Profile tree initial protections)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections) (noCutoff : ∀ index node, area.support index → tree.nodes.get index = some node →
      GeneralBorrowWildcardVirtualLeaf.onlyForeign node maximum = false) :
    ∃ after, GeneralBorrowWildcardVirtualLeafFold.run tree roots initial maximum .Write protections = ⟨after,.Completed⟩ ∧
      WriteFrame initial after ∧ Profile tree after protections ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections :=
  run_from tree initial initial protections roots maximum weights bound data (fun _ => rfl) profile coherent noCutoff

end DuplicatePrefix.GeneralBorrowExposedKnownRootWriteFold
