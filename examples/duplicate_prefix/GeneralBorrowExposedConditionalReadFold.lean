import duplicate_prefix.GeneralBorrowExposedConditionalReadLoop

namespace DuplicatePrefix.GeneralBorrowExposedConditionalReadFold
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafState (ReadFrame)
open GeneralBorrowExposedConditionalReadState
open GeneralBorrowWildcardSubtreeData (Weights)
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Actual source-order virtual-root calls recur on the original raw coherent
counter data. Read counters and protected readability are carried through each
nonleaf source DFS; changed Write counters need no success hypothesis. -/
theorem run_from (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (roots : List UniIndex) (maximum : Option Miri.Memory.BorTag) (weights : Weights tree)
    (bound : ∀ root ∈ roots, weights.weight root ≤ tree.nodes.size)
    (data : ∀ root ∈ roots, Data tree initial root protections)
    (frame : ReadFrame initial current) (readable : Readable tree current protections)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections) (noCutoff : maximum = none) :
    ∃ after, GeneralBorrowWildcardVirtualLeafFold.run tree roots current maximum .Read protections = ⟨after,.Completed⟩ ∧
      ReadFrame initial after ∧ Readable tree after protections ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections := by
  induction roots generalizing current with
  | nil => exact ⟨current,rfl,frame,readable,coherent⟩
  | cons root rest ih =>
    have first := GeneralBorrowExposedConditionalReadLoop.access_from tree initial root maximum protections weights
      (bound root (by simp)) (data root (by simp)) current frame readable coherent noCutoff
    let called := tree.performWildcardAccessAt current root maximum .Read protections true
    obtain ⟨after,tail,afterFrame,afterReadable,afterCoherent⟩ := ih called.location (fun root member => bound root (by simp [member]))
      (fun root member => data root (by simp [member])) first.2.1 first.2.2.1 first.2.2.2
    refine ⟨after,?_,afterFrame,afterReadable,afterCoherent⟩
    have status : (tree.performWildcardAccessAt current root maximum .Read protections true).status = .Completed := first.1
    simpa only [GeneralBorrowWildcardVirtualLeafFold.run,status,beq_self_eq_true,ite_true] using tail

theorem run (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (roots : List UniIndex) (maximum : Option Miri.Memory.BorTag) (weights : Weights tree)
    (bound : ∀ root ∈ roots, weights.weight root ≤ tree.nodes.size)
    (data : ∀ root ∈ roots, Data tree initial root protections)
    (readable : Readable tree initial protections)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections) (noCutoff : maximum = none) :
    ∃ after, GeneralBorrowWildcardVirtualLeafFold.run tree roots initial maximum .Read protections = ⟨after,.Completed⟩ ∧
      ReadFrame initial after ∧ Readable tree after protections ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections :=
  run_from tree initial initial protections roots maximum weights bound data (fun _ => rfl) readable coherent noCutoff

end DuplicatePrefix.GeneralBorrowExposedConditionalReadFold
