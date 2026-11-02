import duplicate_prefix.GeneralBorrowExposedKnownRootWriteFold
import duplicate_prefix.GeneralBorrowExposedKnownRootWritePrimaryLoop
import duplicate_prefix.GeneralBorrowExposedConcreteLast
namespace DuplicatePrefix.GeneralBorrowExposedKnownRootWriteSchedule
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootWriteState
open GeneralBorrowExposedKnownRootWriteState (WriteFrame)
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def run (tree : BorrowTree) (roots : List UniIndex) (selected : UniIndex) (location : LocationTree)
    (maximum : BorTag) (protections : ProtectedTags) : BorrowTree.WildcardLocationAccessResult :=
  match roots with
  | [] => ⟨location,.Completed⟩
  | root::rest =>
    if root = selected then run tree rest selected location maximum protections else
      let called := tree.performWildcardAccessAt location root (some maximum) .Write protections true
      if called.status == .Completed then run tree rest selected called.location maximum protections else called

/-- The source order is retained and every occurrence of the actual selected
root is skipped. Each other component's actual nonleaf virtual call derives
completion from scoped conditional permissions and exact coherent counters. -/
theorem fold_from (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (roots : List UniIndex) (selected : UniIndex) (maximum : BorTag) (weights : Weights tree)
    (bound : ∀ root ∈ roots,weights.weight root ≤ tree.nodes.size)
    (data : ∀ root ∈ roots,root ≠ selected → Data tree initial root protections)
    (frame : WriteFrame initial current) (profile : Profile tree current protections)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (tags : ∀ index node,area.support index → tree.nodes.get index = some node → node.tag.value ≤ maximum.value) :
    ∃ after,run tree roots selected current maximum protections = ⟨after,.Completed⟩ ∧
      WriteFrame initial after ∧ Profile tree after protections ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections := by
  induction roots generalizing current with
  | nil => exact ⟨current,rfl,frame,profile,coherent⟩
  | cons root rest ih =>
    by_cases same : root = selected
    · obtain ⟨after,done,fr,pr,co⟩ := ih current (fun root member => bound root (by simp [member]))
        (fun root member => data root (by simp [member])) frame profile coherent
      exact ⟨after,by simpa only [run,same,ite_true] using done,fr,pr,co⟩
    · have first := GeneralBorrowExposedKnownRootWriteLoop.access_from tree initial root (some maximum) protections weights
        (bound root (by simp)) (data root (by simp) same) current frame profile coherent (by
          intro index node member present
          have bounded := tags index node member present
          simp only [GeneralBorrowWildcardVirtualLeaf.onlyForeign]
          exact decide_eq_false (UInt64.not_lt.mpr bounded))
      let called := tree.performWildcardAccessAt current root (some maximum) .Write protections true
      obtain ⟨after,tail,fr,pr,co⟩ := ih called.location (fun root member => bound root (by simp [member]))
        (fun root member => data root (by simp [member])) first.2.1 first.2.2.1 first.2.2.2
      refine ⟨after,?_,fr,pr,co⟩
      simpa only [run,same,ite_false,show (tree.performWildcardAccessAt current root (some maximum) .Write protections true).status = .Completed from first.1,
        beq_self_eq_true,ite_true] using tail

theorem successful (tree : BorrowTree) (roots : List UniIndex) (selected : UniIndex)
    (before after : LocationTree) (maximum : BorTag) (protections : ProtectedTags) (range : ByteRange)
    (completed : run tree roots selected before maximum protections = ⟨after,.Completed⟩) :
    forIn roots (before,none,false) (GeneralBorrowVirtualRootsAdapter.scan tree selected maximum .Write protections range) = (after,none,false) := by
  induction roots generalizing before with
  | nil => cases completed;rfl
  | cons root rest ih =>
    by_cases same : root = selected
    · simp only [run,same,ite_true] at completed
      rw [List.forIn_cons]
      simpa [GeneralBorrowVirtualRootsAdapter.scan,same,bind,pure] using ih before completed
    · have ne : selected ≠ root := Ne.symm same
      have good : (tree.performWildcardAccessAt before root (some maximum) .Write protections true).status = .Completed := by
        simp only [run,same,ite_false] at completed
        split at completed
        · exact of_decide_eq_true ‹_ = true›
        · have status := congrArg BorrowTree.WildcardLocationAccessResult.status completed
          simp_all
      have tail : run tree rest selected (tree.performWildcardAccessAt before root (some maximum) .Write protections true).location maximum protections = ⟨after,.Completed⟩ := by
        simpa only [run,same,ite_false,good,beq_self_eq_true,ite_true] using completed
      rw [List.forIn_cons]
      simp only [GeneralBorrowVirtualRootsAdapter.scan,show ((none : Option BorrowTree.BorrowTreeAccessStatus) = none ∧ false = false) from ⟨rfl,rfl⟩,
        ite_true,ne,ite_false,good,bind,pure]
      exact ih _ tail
end DuplicatePrefix.GeneralBorrowExposedKnownRootWriteSchedule
