import duplicate_prefix.GeneralBorrowExposedKnownRootSchedule
import duplicate_prefix.GeneralBorrowExposedKnownRootFold
import duplicate_prefix.GeneralBorrowExposedScopedReadFramePrimaryLoop
import duplicate_prefix.GeneralBorrowExposedScopedReadFrameLoop
import duplicate_prefix.GeneralBorrowExposedConcreteLast
namespace DuplicatePrefix.GeneralBorrowExposedScopedReadFrameSchedule
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootState
open GeneralBorrowExposedNonleafState (ReadFrame)
open GeneralBorrowWildcardSubtreeData (Weights)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

open GeneralBorrowExposedKnownRootSchedule (run)
/-- The source order is retained and every occurrence of the actual selected
root is skipped. Each other component's actual nonleaf virtual call derives
completion from scoped conditional permissions and exact coherent counters. -/
theorem fold_from (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (roots : List UniIndex) (selected : UniIndex) (maximum : BorTag) (weights : Weights tree)
    (bound : ∀ root ∈ roots,weights.weight root ≤ tree.nodes.size)
    (data : ∀ root ∈ roots,root ≠ selected → Data tree initial root protections)
    (frame : ReadFrame initial current) (readable : Readable tree current protections)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (tags : ∀ index node,area.support index → tree.nodes.get index = some node → node.tag.value ≤ maximum.value) :
    ∃ after,run tree roots selected current maximum protections = ⟨after,.Completed⟩ ∧
      ReadFrame initial after ∧ Readable tree after protections ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
      (∀ query, ¬area.support query → after.perms.get query = current.perms.get query) := by
  induction roots generalizing current with
  | nil => exact ⟨current,rfl,frame,readable,coherent,fun _ _ => rfl⟩
  | cons root rest ih =>
    by_cases same : root = selected
    · obtain ⟨after,done,fr,pr,co,keep⟩ := ih current (fun root member => bound root (by simp [member]))
        (fun root member => data root (by simp [member])) frame readable coherent
      exact ⟨after,by simpa only [run,same,ite_true] using done,fr,pr,co,keep⟩
    · have first := GeneralBorrowExposedScopedReadFrameLoop.access_from tree initial root (some maximum) protections weights
        (bound root (by simp)) (data root (by simp) same) current frame readable coherent (by
          intro index node member present
          have bounded := tags index node member present
          simp only [GeneralBorrowWildcardVirtualLeaf.onlyForeign]
          exact decide_eq_false (UInt64.not_lt.mpr bounded))
      let called := tree.performWildcardAccessAt current root (some maximum) .Read protections true
      obtain ⟨after,tail,fr,pr,co,keep⟩ := ih called.location (fun root member => bound root (by simp [member]))
        (fun root member => data root (by simp [member])) first.2.1 first.2.2.1 first.2.2.2.1
      refine ⟨after,?_,fr,pr,co,fun query outside => (keep query outside).trans (first.2.2.2.2 query outside)⟩
      simpa only [run,same,ite_false,show (tree.performWildcardAccessAt current root (some maximum) .Read protections true).status = .Completed from first.1,
        beq_self_eq_true,ite_true] using tail

end DuplicatePrefix.GeneralBorrowExposedScopedReadFrameSchedule
