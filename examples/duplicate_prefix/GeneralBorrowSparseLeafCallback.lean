import duplicate_prefix.GeneralBorrowSparseLeafPhysical
namespace DuplicatePrefix.GeneralBorrowSparseLeafCallback
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf GeneralBorrowSparseLeafPhysical GeneralBorrowSparseExposedLeafState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

def Writable (tree : BorrowTree) (protections : ProtectedTags) (support : UniIndex→Prop) (location : LocationTree) : Prop :=
  ∀index node,support index→tree.nodeAt index=some node→GeneralBorrowExposedConditionalWritePermissions.Compatible
    (effective location index node) .LocalAccess (protections.contains node.tag)

theorem coherent_levels (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree before protections) (cache : after.exposedCache=before.exposedCache)
    (levels : ∀index node,tree.nodeAt index=some node→GeneralBorrowExposureCardinality.effective after protections index node=
      GeneralBorrowExposureCardinality.effective before protections index node) :
    GeneralBorrowExposureCardinality.LocationCoherent tree after protections := by
  intro query kind
  rw [cache,coherent query kind]
  unfold GeneralBorrowExposureCardinality.cardinality
  apply congrArg UInt16.ofNat
  apply congrArg List.length
  apply List.filter_congr
  intro row member
  have present:=(GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
  simp only [GeneralBorrowExposureCardinality.contributes,levels row.1 row.2 present]

/-- Every real old-leaf physical or virtual callback completes from effective
mutable scalar data. Physical callbacks may materialize/change a reservation;
virtual callbacks really materialize lazy defaults. Coherence, all writable
leaves, the full cache, and every other permission row are retained. -/
theorem step (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (support : UniIndex→Prop)
    (root : UniIndex) (node : TreeNode) (maximum : Option BorTag) (kind : AccessKind) (virtual : Bool)
    (present : tree.nodeAt root=some node) (leaf : node.children=#[]) (exposed : node.isExposed=true) (included : support root)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections) (short : tree.nodes.size<65536)
    (writable : Writable tree protections support location) (bound : ∀tag,maximum=some tag→node.tag.value≤tag.value) :
    ∃after,tree.performWildcardAccessAt location root maximum kind protections virtual=⟨after,.Completed⟩ ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧ after.exposedCache=location.exposedCache ∧
      Writable tree protections support after ∧
      (∀query,query≠root→after.perms.get query=location.perms.get query) := by
  have good:=writable root node included present
  have positive:=GeneralBorrowExposureCardinality.exposed_self location.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective location protections) coherent short root node present exposed kind (supports _ _ good kind)
  rw [counter_count] at positive
  have nonzero:=Nat.ne_of_gt positive
  cases virtual with
  | false=>
    obtain ⟨after,actual,cache,next,others⟩:=GeneralBorrowSparseLeafPhysical.access tree location root node maximum kind protections present leaf exposed bound nonzero good
    have coherentAfter : GeneralBorrowExposureCardinality.LocationCoherent tree after protections := by
      apply coherent_levels tree location after protections coherent cache
      intro query queryNode queryPresent
      by_cases same : query=root
      · subst query
        have nodeEq:=Option.some.inj (present.symm.trans queryPresent)
        subst queryNode
        change (effective after root node).permission.strongestAllowedLocalAccess _=(effective location root node).permission.strongestAllowedLocalAccess _
        rw [level_write _ _ next,level_write _ _ good]
      · simp only [GeneralBorrowExposureCardinality.effective,effective,others query same]
    refine ⟨after,actual,coherentAfter,cache,?_,others⟩
    intro query queryNode member found
    by_cases same : query=root
    · subst query
      have nodeEq:=Option.some.inj (present.symm.trans found)
      subst queryNode
      exact next
    · simpa only [effective,others query same] using writable query queryNode member found
  | true=>
    have cutoff : onlyForeign node maximum=false := by
      cases maximum with
      | none=>rfl
      | some tag=>simp only [onlyForeign];exact decide_eq_false (UInt64.not_lt.mpr (bound tag rfl))
    let after:=materialized location root node
    have frame:=GeneralBorrowExposedVirtualSchedule.materialized_effective tree location root node present
    refine ⟨after,GeneralBorrowWildcardVirtualLeaf.either_access tree location root node maximum kind protections present leaf nonzero cutoff,
      GeneralBorrowExposedVirtualSchedule.coherent_frame tree location after protections coherent rfl frame,rfl,?_,?_⟩
    · intro query queryNode member found
      rw [show effective after query queryNode=effective location query queryNode from frame query queryNode found]
      exact writable query queryNode member found
    · intro query different
      unfold after materialized UniValMap.orInsert
      split
      · rfl
      · exact GeneralBorrowFreshLocation.get_other _ root query node.defaultLocationState different
end
end DuplicatePrefix.GeneralBorrowSparseLeafCallback
