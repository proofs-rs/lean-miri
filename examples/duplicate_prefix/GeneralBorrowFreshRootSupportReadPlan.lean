import duplicate_prefix.GeneralBorrowFreshRootSupportCutoff
import duplicate_prefix.GeneralBorrowSnapshotPrimaryReadPlan
namespace DuplicatePrefix.GeneralBorrowFreshRootSupportReadPlan
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSnapshotReadDFSPlan GeneralBorrowWildcardControlStack GeneralBorrowWildcardSubtreeStack
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem known_pop {tree : BorrowTree} {root : UniIndex} (support : Support tree root)
    (stack : Array Task) (task : Task) (known : ∀ item ∈ (stack.push task).toList, support.contains item.1) :
    ∀ item ∈ stack.toList, support.contains item.1 := by
  intro item member
  exact known item (by simp [member])

/-- Lift no-cutoff witness bookkeeping to a support-bounded cutoff. The pending
invariant itself records actual stack support, so no parent tag order or bound
on hidden nodes in other physical components is required. -/
def lift (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags) (root : UniIndex)
    (maximum : BorTag) (support : Support tree root)
    (bounded : GeneralBorrowFreshRootSupportCutoff.SupportBound tree maximum support.contains)
    (plan : WitnessPlan tree initial protections root 0 none) :
    WitnessPlan tree initial protections root 0 (some maximum) where
  pending := fun seen stack => plan.pending seen stack ∧ ∀ task ∈ stack.toList,support.contains task.1
  initial := ⟨plan.initial,by
    intro task member
    have same : task = (root,false) := by simpa using member
    subst task
    exact support.rooted⟩
  finish := by intro seen pending;exact plan.finish seen pending.1
  pop := by
    intro location seen stack index node present frame pending skipped
    have included : support.contains index := pending.2 (index,false) (by simp)
    have same : relation location root index node (some maximum) .Read 0 = relation location root index node none .Read 0 := by
      simp only [relation,GeneralBorrowFreshRootCutoff.above node maximum (bounded index node included present)]
    rw [same] at skipped
    exact ⟨plan.pop location seen stack index node present frame pending.1 skipped,
      known_pop support stack (index,false) pending.2⟩
  expand := by
    intro seen stack index node present pending
    have included : support.contains index := pending.2 (index,false) (by simp)
    refine ⟨plan.expand seen stack index node present pending.1,?_⟩
    intro task member
    simp only [expanded,Array.toList_append,Array.toList_push,Array.toList_map,List.mem_append] at member
    rcases member with earlier | child
    · rcases earlier with previous | same
      · exact pending.2 task (by simp [previous])
      · have equal : task = (index,true) := by simpa using same
        subst task
        exact included
    · obtain ⟨query,member,equal⟩ := List.mem_map.mp child
      subst task
      exact support.children index node included present query member
  post := by
    intro location seen stack index node present frame pending
    have included : support.contains index := pending.2 (index,true) (by simp)
    have allowed : (decide (node.tag.value ≤ maximum.value) : Bool) = true := by
      simpa only [decide_eq_true_eq] using bounded index node included present
    have same : GeneralBorrowSnapshotReadDFSPlan.seen location index node (some maximum) protections seen = GeneralBorrowSnapshotReadDFSPlan.seen location index node none protections seen := by
      simp only [GeneralBorrowSnapshotReadDFSPlan.seen,Option.isNone_some,Option.any_some,Option.isNone_none,Option.any_none,
        allowed,Bool.false_or,Bool.true_or]
    rw [same]
    exact ⟨plan.post location seen stack index node present frame pending.1,
      known_pop support stack (index,true) pending.2⟩

/-- Raw finite callback authorization forms this support-bounded primary Read
plan internally. It accepts no successful visitor or future capability. -/
theorem of_authorization (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (maximum : BorTag) (support : UniIndex → Prop)
    (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree maximum)
    (bounded : GeneralBorrowFreshRootSupportCutoff.SupportBound tree maximum support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : GeneralBorrowExposedNonleafPrimaryPath.Reciprocal tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (authorization : Authorization tree initial protections root 0 (some maximum) .Read support) :
    Nonempty (WitnessPlan tree initial protections root 0 (some maximum)) := by
  have noMaximum := (GeneralBorrowFreshRootSupportCutoff.authorization_iff tree initial protections maximum exposed root 0 .Read support bounded).mpr authorization
  obtain ⟨plan⟩ := GeneralBorrowSnapshotPrimaryReadPlan.of_authorization tree initial protections root support depth graph coherent short noMaximum
  exact ⟨lift tree initial protections root maximum (Support.of_authorization tree initial protections root 0 (some maximum) .Read support authorization) bounded plan⟩
end DuplicatePrefix.GeneralBorrowFreshRootSupportReadPlan
