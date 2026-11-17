import duplicate_prefix.GeneralBorrowFreshRootSupportReadPlan
import duplicate_prefix.DuplicatePrefixResidualWriteWitnessPlan
namespace DuplicatePrefix.GeneralBorrowFreshRootSupportWritePlan
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixResidualWriteWitnessPlan GeneralBorrowWildcardControlStack GeneralBorrowWildcardSubtreeStack
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization GeneralBorrowWildcardControlWitness
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem known_pop {tree : BorrowTree} {root : UniIndex} (support : Support tree root)
    (stack : Array Task) (task : Task) (known : ∀ item ∈ (stack.push task).toList, support.contains item.1) :
    ∀ item ∈ stack.toList, support.contains item.1 := by
  intro item member
  exact known item (by simp [member])

private theorem model_none (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (maximum : BorTag) (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree maximum)
    (model : Model tree initial current protections (some maximum)) : Model tree initial current protections none := by
  obtain ⟨removed,legal,matching⟩ := model
  refine ⟨removed,⟨legal.distinct,?_⟩,matching⟩
  intro index member
  obtain ⟨node,present,allowed⟩ := legal.allowed index member
  exact ⟨node,present,by
    rw [←GeneralBorrowFreshRootSupportCutoff.removable_eq tree initial protections maximum exposed index node present .Write]
    exact allowed⟩

/-- Actual Write ghost bookkeeping keeps known DFS support and the exact finite
removal model. Exposed contributors are bounded globally; newer hidden nodes
outside this old-root support remain arbitrary. -/
def lift (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags) (root : UniIndex)
    (maximum : BorTag) (support : Support tree root)
    (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree maximum)
    (bounded : GeneralBorrowFreshRootSupportCutoff.SupportBound tree maximum support.contains)
    (plan : Plan tree initial protections root 0 none) : Plan tree initial protections root 0 (some maximum) where
  pending := fun seen stack => plan.pending seen stack ∧ ∀ task ∈ stack.toList,support.contains task.1
  initial := ⟨plan.initial,by
    intro task member
    have same : task = (root,false) := by simpa using member
    subst task
    exact support.rooted⟩
  finish := by intro seen pending;exact plan.finish seen pending.1
  pop := by
    intro current seen stack index node present model coherent pending skipped
    have included : support.contains index := pending.2 (index,false) (by simp)
    have same : relation current root index node (some maximum) .Write 0 = relation current root index node none .Write 0 := by
      simp only [relation,GeneralBorrowFreshRootCutoff.above node maximum (bounded index node included present)]
    rw [same] at skipped
    exact ⟨plan.pop current seen stack index node present (model_none tree initial current protections maximum exposed model)
      coherent pending.1 skipped,known_pop support stack (index,false) pending.2⟩
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
    intro current seen stack index node present model pending
    have included : support.contains index := pending.2 (index,true) (by simp)
    have allowed : (decide (node.tag.value ≤ maximum.value) : Bool) = true := by
      simpa only [decide_eq_true_eq] using bounded index node included present
    have same : DuplicatePrefixResidualWriteDFSInvariant.seen current index node (some maximum) protections seen =
        DuplicatePrefixResidualWriteDFSInvariant.seen current index node none protections seen := by
      simp only [DuplicatePrefixResidualWriteDFSInvariant.seen,Option.isNone_some,Option.any_some,Option.isNone_none,Option.any_none,
        allowed,Bool.false_or,Bool.true_or]
    rw [same]
    exact ⟨plan.post current seen stack index node present (model_none tree initial current protections maximum exposed model)
      pending.1,known_pop support stack (index,true) pending.2⟩

/-- Current raw callback data derive the complete fresh-cutoff primary Write
plan. There is no supplied traversal success, future permission or parent order. -/
theorem of_authorization (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (maximum : BorTag) (support : UniIndex → Prop)
    (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree maximum)
    (bounded : GeneralBorrowFreshRootSupportCutoff.SupportBound tree maximum support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : GeneralBorrowExposedNonleafPrimaryPath.Reciprocal tree)
    (short : tree.nodes.size < 65536)
    (authorization : Authorization tree initial protections root 0 (some maximum) .Write support) :
    Nonempty (Plan tree initial protections root 0 (some maximum)) := by
  have noMaximum := (GeneralBorrowFreshRootSupportCutoff.authorization_iff tree initial protections maximum exposed root 0 .Write support bounded).mpr authorization
  obtain ⟨witness,node,included,present,eligible⟩ := noMaximum.witness rfl
  have path := path_of_covers tree depth root witness node present (noMaximum.covers witness included)
  let plan := DuplicatePrefixResidualWriteWitnessPlan.primary tree initial protections root witness node present eligible path depth graph short
  exact ⟨lift tree initial protections root maximum
    (Support.of_authorization tree initial protections root 0 (some maximum) .Write support authorization) exposed bounded plan⟩
end DuplicatePrefix.GeneralBorrowFreshRootSupportWritePlan
