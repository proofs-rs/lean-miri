import duplicate_prefix.DuplicatePrefixResidualCountModel
namespace DuplicatePrefix.DuplicatePrefixResidualWriteQueries
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixResidualCountModel
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- A legal removal consists of initial exposed Write supporters. Exact
unvisited scalar equality and Matches rule out removal of the current node;
absence from the removal set is derived, rather than used as unvisitedness. -/
theorem unvisited_not_removed (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (removed : List UniIndex)
    (legal : Removal tree initial protections maximum .Write removed)
    (matching : Matches tree initial current protections .Write removed)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (unvisited : current.perms.get index = initial.perms.get index) : index ∉ removed := by
  intro member
  obtain ⟨old,found,allowed⟩ := legal.allowed index member
  have same : old = node := Option.some.inj (found.symm.trans present)
  subst old
  have exposed : node.isExposed = true := by
    simp only [removable, Bool.and_eq_true] at allowed
    exact allowed.1.1.1
  have initialSupport : GeneralBorrowExposureCardinality.supports
      (GeneralBorrowExposureCardinality.effective initial protections index node) .Write = true := by
    simp only [removable, Bool.and_eq_true] at allowed
    exact allowed.1.2
  have masked := matching index node present exposed
  rw [show GeneralBorrowExposureCardinality.effective current protections index node =
      GeneralBorrowExposureCardinality.effective initial protections index node by
    simp only [GeneralBorrowExposureCardinality.effective,unvisited], initialSupport] at masked
  simp [levels,member,GeneralBorrowExposureCardinality.supports,
    GeneralBorrowExposureAncestorFold.supportsWrite] at masked

/-- An arbitrary nested pair of legal finite removals supplies the source's
actual entry/exit query authorization. Both snapshots retain the exact initial
scalar entry at this unvisited node. No DFS result is assumed. -/
theorem queries (tree : BorrowTree) (initial beforeCurrent afterCurrent : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat) (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support)
    (before after : List UniIndex)
    (legalBefore : Removal tree initial protections maximum .Write before)
    (legalAfter : Removal tree initial protections maximum .Write after)
    (subset : ∀ query ∈ before, query ∈ after)
    (matchingBefore : Matches tree initial beforeCurrent protections .Write before)
    (matchingAfter : Matches tree initial afterCurrent protections .Write after)
    (coherentBefore : GeneralBorrowExposureCardinality.LocationCoherent tree beforeCurrent protections)
    (coherentAfter : GeneralBorrowExposureCardinality.LocationCoherent tree afterCurrent protections)
    (short : tree.nodes.size < 65536) (inside : support index) (present : tree.nodes.get index = some node)
    (unvisitedBefore : beforeCurrent.perms.get index = initial.perms.get index)
    (unvisitedAfter : afterCurrent.perms.get index = initial.perms.get index) :
    ((beforeCurrent.perms.get index).getD node.defaultLocationState =
      (afterCurrent.perms.get index).getD node.defaultLocationState) ∧
    DuplicatePrefixCallbackVisitAuthorization.Authorized
      ((afterCurrent.perms.get index).getD node.defaultLocationState) .Write (protections.contains node.tag)
      (relation beforeCurrent root index node maximum .Write rootPosition)
      (relation afterCurrent root index node maximum .Write rootPosition) := by
  refine ⟨by rw [unvisitedBefore,unvisitedAfter],?_⟩
  have retained := unvisited_not_removed tree initial afterCurrent protections maximum after legalAfter matchingAfter index node present unvisitedAfter
  have raw := authorization.queries before after legalBefore legalAfter subset index node inside present retained
  rw [relation_matches tree initial beforeCurrent protections .Write before matchingBefore coherentBefore short root index node maximum rootPosition,
    relation_matches tree initial afterCurrent protections .Write after matchingAfter coherentAfter short root index node maximum rootPosition,
    unvisitedAfter]
  exact raw

/-- After an actual non-skipped entry, the authorized recomputed exit query
is Either (no scalar access), or its real record/access branch succeeds. The
query pair may contain arbitrary nested legal removals; counters are supplied
by actual coherence and Matches, not assumed traversal success. -/
theorem exit_transition (tree : BorrowTree) (initial beforeCurrent afterCurrent : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (rootPosition : Nat) (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root rootPosition maximum .Write support)
    (before after : List UniIndex)
    (legalBefore : Removal tree initial protections maximum .Write before)
    (legalAfter : Removal tree initial protections maximum .Write after)
    (subset : ∀ query ∈ before, query ∈ after)
    (matchingBefore : Matches tree initial beforeCurrent protections .Write before)
    (matchingAfter : Matches tree initial afterCurrent protections .Write after)
    (coherentBefore : GeneralBorrowExposureCardinality.LocationCoherent tree beforeCurrent protections)
    (coherentAfter : GeneralBorrowExposureCardinality.LocationCoherent tree afterCurrent protections)
    (short : tree.nodes.size < 65536) (inside : support index) (present : tree.nodes.get index = some node)
    (unvisitedBefore : beforeCurrent.perms.get index = initial.perms.get index)
    (unvisitedAfter : afterCurrent.perms.get index = initial.perms.get index)
    (notSkipped : DuplicatePrefixCallbackVisitAuthorization.entrySkip
      ((beforeCurrent.perms.get index).getD node.defaultLocationState) .Write
      (relation beforeCurrent root index node maximum .Write rootPosition) = false) :
    ∃ related, relation afterCurrent root index node maximum .Write rootPosition = some related ∧
      (related = .EitherAccess ∨ ∃ exact recorded next delta,
        exactRelation related = some exact ∧
        ((afterCurrent.perms.get index).getD node.defaultLocationState).recordNewAccess .Write exact = .Recorded recorded ∧
        recorded.performAccess .Write exact (protections.contains node.tag) = .Success next delta) := by
  obtain ⟨same,authorized⟩ := queries tree initial beforeCurrent afterCurrent protections root index node maximum rootPosition support
    authorization before after legalBefore legalAfter subset matchingBefore matchingAfter coherentBefore coherentAfter short inside present unvisitedBefore unvisitedAfter
  rw [same] at notSkipped
  exact DuplicatePrefixCallbackVisitAuthorization.exit_transition _ .Write _ _ _ authorized notSkipped
end DuplicatePrefix.DuplicatePrefixResidualWriteQueries
