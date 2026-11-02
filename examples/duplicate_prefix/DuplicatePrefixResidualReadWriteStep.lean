import duplicate_prefix.DuplicatePrefixResidualWriteStep
import duplicate_prefix.DuplicatePrefixResidualReadWriteSupport
namespace DuplicatePrefix.DuplicatePrefixResidualReadWriteStep
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixResidualCountModel
open GeneralBorrowProtectedReadCompatible (Compatible)
open GeneralBorrowExposedConditionalWritePermissions (support)
open DuplicatePrefixResidualWriteStep (Lost removedAfter loss_fresh updated_matches)
open GeneralBorrowExposedNonleafState (updated updated_other)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- One actual exact Read node visit advances the finite residual model.
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
    (source : relation current root index node maximum .Read rootPosition = some query)
    (exactQuery : exactRelation query = some related)
    (compatible : Compatible ((current.perms.get index).getD node.defaultLocationState) related (protections.contains node.tag))
    (scheduled : GeneralBorrowEvents.Scheduled ((current.perms.get index).getD node.defaultLocationState) .Read related) :
    ∃ recorded next delta,
      ((current.perms.get index).getD node.defaultLocationState).recordNewAccess .Read related = .Recorded recorded ∧
      recorded.performAccess .Read related (protections.contains node.tag) = .Success next delta ∧
      Compatible next related (protections.contains node.tag) ∧
      Removal tree initial protections maximum .Write (removedAfter current protections removed index node next) ∧
      Matches tree initial (updated tree current index node protections recorded next delta) protections .Write
        (removedAfter current protections removed index node next) ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree (updated tree current index node protections recorded next delta) protections ∧
      (∀ query, query ≠ index → (updated tree current index node protections recorded next delta).perms.get query = current.perms.get query) := by
  obtain ⟨recorded,next,delta,record,actual,good,noGain,lossPermission⟩ :=
    DuplicatePrefixResidualReadWriteSupport.visit _ related _ compatible scheduled
  refine ⟨recorded,next,delta,record,actual,good,?_,
    updated_matches tree initial current protections removed matching index node present recorded next delta noGain,
    GeneralBorrowExposedNonleafCoherence.updated_coherent tree current index node protections recorded next delta related
      depth present coherent record actual,
    fun query different => updated_other tree current index query node protections recorded next delta different⟩
  by_cases loss : Lost current protections index node next
  · have fresh := loss_fresh tree initial current protections removed matching index node present next loss
    obtain ⟨foreign,permission⟩ := lossPermission loss.2.1 loss.2.2
    have queryForeign : query = .ForeignAccess := by cases query <;> simp_all [exactRelation]
    subst query
    have above := DuplicatePrefixResidualReadWriteSupport.source_read_foreign_above tree current protections root index node maximum rootPosition
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
end DuplicatePrefix.DuplicatePrefixResidualReadWriteStep
