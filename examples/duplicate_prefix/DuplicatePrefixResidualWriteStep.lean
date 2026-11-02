import duplicate_prefix.DuplicatePrefixResidualWriteTransition
import duplicate_prefix.DuplicatePrefixResidualCountModel
import duplicate_prefix.GeneralBorrowExposedConditionalWriteCoherence
namespace DuplicatePrefix.DuplicatePrefixResidualWriteStep
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixResidualCountModel GeneralBorrowExposedConditionalWritePermissions
open GeneralBorrowExposedNonleafState (updated updated_other)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def Lost (current : LocationTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (next : LocationState) : Prop :=
  node.isExposed = true ∧ support ((current.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) = true ∧
    support next (protections.contains node.tag) = false
instance (current : LocationTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (next : LocationState) : Decidable (Lost current protections index node next) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def removedAfter (current : LocationTree) (protections : ProtectedTags) (removed : List UniIndex)
    (index : UniIndex) (node : TreeNode) (next : LocationState) : List UniIndex :=
  if Lost current protections index node next then index :: removed else removed

theorem loss_fresh (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (removed : List UniIndex) (matching : Matches tree initial current protections .Write removed)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) (next : LocationState)
    (loss : Lost current protections index node next) : index ∉ removed := by
  intro member
  have count := matching index node present loss.1
  change support ((current.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) = _ at count
  rw [loss.2.1] at count
  simp [levels, member, GeneralBorrowExposureCardinality.supports, GeneralBorrowExposureAncestorFold.supportsWrite] at count

theorem updated_matches (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (removed : List UniIndex) (matching : Matches tree initial current protections .Write removed)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (recorded next : LocationState) (delta : PermTransition)
    (noGain : support ((current.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) = false →
      support next (protections.contains node.tag) = false) :
    Matches tree initial (updated tree current index node protections recorded next delta) protections .Write
      (removedAfter current protections removed index node next) := by
  intro query queryNode found exposed
  by_cases same : query = index
  · subst query
    have nodeEq : queryNode = node := Option.some.inj (found.symm.trans present)
    subst queryNode
    have old := matching index node present exposed
    change support ((current.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) = _ at old
    change support (((updated tree current index node protections recorded next delta).perms.get index).getD node.defaultLocationState)
      (protections.contains node.tag) = _
    simp only [updated, GeneralBorrowWildcardSubtreeState.write_same, Option.getD_some]
    by_cases loss : Lost current protections index node next
    · have masked : GeneralBorrowExposureCardinality.supports
          (levels initial protections (removedAfter current protections removed index node next) index node) .Write = false := by
        simp [removedAfter, loss, levels, GeneralBorrowExposureCardinality.supports,
          GeneralBorrowExposureAncestorFold.supportsWrite]
      rw [masked]
      exact loss.2.2
    · have sameSupport : support next (protections.contains node.tag) =
          support ((current.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) := by
        cases before : support ((current.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) <;>
          cases after : support next (protections.contains node.tag) <;> simp_all [Lost]
      simpa only [removedAfter, if_neg loss] using sameSupport.trans old
  · simp only [GeneralBorrowExposureCardinality.effective,
      updated_other tree current index query node protections recorded next delta same]
    have old := matching query queryNode found exposed
    change GeneralBorrowExposureCardinality.supports
      (((current.perms.get query).getD queryNode.defaultLocationState).permission.strongestAllowedLocalAccess (protections.contains queryNode.tag)) .Write = _ at old
    rw [old]
    unfold removedAfter
    split
    · simp [levels, same]
    · rfl
/-- One actual exact Write node visit advances the finite residual model.
Unvisited means literal equality of the initial/current stored permission
entry; membership outside the removal set alone is deliberately insufficient.
All successful record/access and updated-cache facts are conclusions. -/
theorem step (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat)
    (removed : List UniIndex) (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial current protections .Write removed)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections)
    (short : tree.nodes.size < 65536) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (present : tree.nodes.get index = some node)
    (unvisited : current.perms.get index = initial.perms.get index)
    (query : WildcardAccessRelatedness) (related : AccessRelatedness)
    (source : relation current root index node maximum .Write rootPosition = some query)
    (exactQuery : exactRelation query = some related)
    (compatible : Compatible ((current.perms.get index).getD node.defaultLocationState) related (protections.contains node.tag))
    (scheduled : GeneralBorrowEvents.Scheduled ((current.perms.get index).getD node.defaultLocationState) .Write related) :
    ∃ recorded next delta,
      ((current.perms.get index).getD node.defaultLocationState).recordNewAccess .Write related = .Recorded recorded ∧
      recorded.performAccess .Write related (protections.contains node.tag) = .Success next delta ∧
      Compatible next related (protections.contains node.tag) ∧
      Removal tree initial protections maximum .Write (removedAfter current protections removed index node next) ∧
      Matches tree initial (updated tree current index node protections recorded next delta) protections .Write
        (removedAfter current protections removed index node next) ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree (updated tree current index node protections recorded next delta) protections := by
  obtain ⟨recorded,next,delta,record,actual,good,noGain,lossPermission⟩ :=
    DuplicatePrefixResidualWriteTransition.visit _ related _ compatible scheduled
  refine ⟨recorded,next,delta,record,actual,good,?_,
    updated_matches tree initial current protections removed matching index node present recorded next delta noGain,
    GeneralBorrowExposedConditionalWriteCoherence.updated_coherent tree current index node protections recorded next delta related
      depth present coherent record actual⟩
  by_cases loss : Lost current protections index node next
  · have fresh := loss_fresh tree initial current protections removed matching index node present next loss
    obtain ⟨foreign,permission⟩ := lossPermission loss.2.1 loss.2.2
    have queryForeign : query = .ForeignAccess := by cases query <;> simp_all [exactRelation]
    subst query
    have above := DuplicatePrefixResidualWriteTransition.source_foreign_above tree current protections root index node maximum rootPosition
      coherent short present loss.1 loss.2.1 source
    have allowed : removable current protections maximum .Write index node = true := by
      change node.isExposed && aboveMaximum node maximum &&
        support ((current.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) &&
        losesWriteWhenForeign ((current.perms.get index).getD node.defaultLocationState).permission = true
      simp [loss.1,above,loss.2.1,permission]
    have initialAllowed : removable initial protections maximum .Write index node = true := by
      simpa only [removable,GeneralBorrowExposureCardinality.effective,unvisited] using allowed
    simpa only [removedAfter, if_pos loss] using
      removal_cons tree initial protections maximum .Write removed legal index fresh node present initialAllowed
  · simpa only [removedAfter, if_neg loss] using legal
end DuplicatePrefix.DuplicatePrefixResidualWriteStep
