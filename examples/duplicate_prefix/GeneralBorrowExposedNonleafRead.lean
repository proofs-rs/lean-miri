import duplicate_prefix.GeneralBorrowExposureCardinality
import duplicate_prefix.GeneralBorrowProtectedReadInvariant
import duplicate_prefix.GeneralBorrowExposurePermissionUpdate

namespace DuplicatePrefix.GeneralBorrowExposedNonleafRead
open Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Raw subtree coverage and coherent finite-width counters determine every
virtual Read classification, including internal nodes with arbitrary children. -/
theorem classify (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root query : UniIndex) (onlyForeign : Bool)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (covers : GeneralBorrowExposureCardinality.Covers tree.nodes root query) :
    location.exposedCache.accessRelatedness root query .Read true onlyForeign =
      some (if onlyForeign || GeneralBorrowWildcardRelatednessBounds.count location.exposedCache query .Read == 0
        then .ForeignAccess else .EitherAccess) := by
  apply GeneralBorrowWildcardRelatednessBounds.virtual_classify
  exact GeneralBorrowExposureCardinality.dominates location.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective location protections) coherent short root query covers .Read

/-- An exposed supporting descendant supplies a positive root counter without
requiring the root or any intermediate node to be a leaf or itself exposed. -/
theorem exposed_descendant (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (root witness : UniIndex) (node : TreeNode)
    (present : tree.nodes.get witness = some node) (exposed : node.isExposed = true)
    (supported : GeneralBorrowExposureCardinality.supports
      (GeneralBorrowExposureCardinality.effective location protections witness node) .Read = true)
    (ancestor : root ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) witness) :
    0 < (GeneralBorrowExposureCardinality.counter location.exposedCache root .Read).toNat := by
  rw [GeneralBorrowExposureCardinality.nat_exact location.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective location protections) coherent short root .Read]
  apply List.length_pos_iff.mpr
  intro absent
  have member : (witness,node) ∈ tree.nodes.entries.toList.filter
      (GeneralBorrowExposureCardinality.contributes tree.nodes
        (GeneralBorrowExposureCardinality.effective location protections) root .Read) := by
    refine List.mem_filter.mpr ⟨(GeneralBorrowFreshReuseProtection.entries_get tree.nodes witness node).mpr present,?_⟩
    simp only [GeneralBorrowExposureCardinality.contributes,exposed,supported,Bool.true_and]
    exact List.contains_iff_mem.mpr ancestor
  rw [absent] at member
  cases member

/-- Exact Read transitions preserve the universal protected Read profile and
Read support. The write strength may change, so cache updates remain necessary. -/
theorem transition (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (initial : GeneralBorrowProtectedReadInvariant.Readable state held) :
    ∃ next delta, state.performAccess .Read related held = .Success next delta ∧
      GeneralBorrowProtectedReadInvariant.Readable next held ∧
      GeneralBorrowExposureCardinality.supports (next.permission.strongestAllowedLocalAccess held) .Read =
        GeneralBorrowExposureCardinality.supports (state.permission.strongestAllowedLocalAccess held) .Read := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [GeneralBorrowProtectedReadInvariant.Readable,LocationState.possible,Permission.isUnique] at initial <;>
      (refine ⟨_,_,rfl,?_,?_⟩; all_goals simp [GeneralBorrowProtectedReadInvariant.Readable,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign,GeneralBorrowExposureCardinality.supports,Permission.strongestAllowedLocalAccess,GeneralBorrowExposureAncestorFold.supportsRead])
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [GeneralBorrowProtectedReadInvariant.Readable,LocationState.possible,Permission.isUnique] at initial <;>
      (refine ⟨_,_,rfl,?_,?_⟩; all_goals simp [GeneralBorrowProtectedReadInvariant.Readable,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign,GeneralBorrowExposureCardinality.supports,Permission.strongestAllowedLocalAccess,GeneralBorrowExposureAncestorFold.supportsRead])

/-- A scheduled exact visit derives both source recording and transition
success from the permission/SIFA profile, retaining support for later visits. -/
theorem visit (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (initial : GeneralBorrowProtectedReadInvariant.Readable state held)
    (scheduled : GeneralBorrowEvents.Scheduled state .Read related) :
    ∃ recorded next delta, state.recordNewAccess .Read related = .Recorded recorded ∧
      recorded.performAccess .Read related held = .Success next delta ∧
      GeneralBorrowProtectedReadInvariant.Readable next held ∧
      GeneralBorrowExposureCardinality.supports (next.permission.strongestAllowedLocalAccess held) .Read =
        GeneralBorrowExposureCardinality.supports (state.permission.strongestAllowedLocalAccess held) .Read := by
  let recorded := {state with idempotentForeignAccess := (IdempotentForeignAccess.recordNew state.idempotentForeignAccess
    (IdempotentForeignAccess.fromAccessAndRelatedness .Read related))}
  have good : GeneralBorrowProtectedReadInvariant.Readable recorded held := initial
  obtain ⟨next,delta,actual,readable,support⟩ := transition recorded related held good
  refine ⟨recorded,next,delta,?_,actual,readable,support⟩
  simp only [LocationState.recordNewAccess,GeneralBorrowEvents.scheduled_recurse state .Read related scheduled,
    beq_self_eq_true,↓reduceIte]
  rfl

/-- The real conditional ancestor-cache update preserves every Read counter
when the changed row retains Read support. Write counters are unrestricted. -/
theorem update_read_counter (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (depth : DuplicatePrefix.GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node)
    (next : LocationState)
    (sameRead : GeneralBorrowExposureCardinality.supports
      (next.permission.strongestAllowedLocalAccess (protections.contains node.tag)) .Read =
      GeneralBorrowExposureCardinality.supports
        (GeneralBorrowExposureCardinality.effective location protections index node) .Read)
    (query : UniIndex) :
    GeneralBorrowExposureCardinality.counter
      (GeneralBorrowExposurePermissionUpdate.cacheUpdate tree location protections index node next).cache query .Read =
      GeneralBorrowExposureCardinality.counter location.exposedCache query .Read := by
  have updated := GeneralBorrowExposurePermissionUpdate.preserves tree location protections depth coherent index node present next
  change GeneralBorrowExposureCardinality.counter (GeneralBorrowExposurePermissionUpdate.nextLocation tree location protections index node next).exposedCache query .Read = _
  rw [updated.2 query .Read,coherent query .Read]
  apply congrArg UInt16.ofNat
  unfold GeneralBorrowExposureCardinality.cardinality
  apply congrArg List.length
  apply List.filter_congr
  intro row member
  have found := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
  unfold GeneralBorrowExposureCardinality.contributes
  by_cases same : row.1 = index
  · have foundAt : tree.nodes.get index = some row.2 := by simpa only [same] using found
    have sameNode : row.2 = node := Option.some.inj (foundAt.symm.trans present)
    simp only [same,sameNode,GeneralBorrowExposureCardinality.effective,
      GeneralBorrowExposurePermissionUpdate.nextLocation,GeneralBorrowFreshLocation.get_same,Option.getD_some]
    rw [sameRead]
    rfl
  · simp only [GeneralBorrowExposureCardinality.effective,GeneralBorrowExposurePermissionUpdate.nextLocation,
      GeneralBorrowFreshLocation.get_other _ index row.1 next same]

/-- One exact nonleaf Read visit includes its genuine conditional source
cache update, whose success and coherent output follow from raw graph data. -/
theorem visit_cache (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node)
    (related : AccessRelatedness)
    (readable : GeneralBorrowProtectedReadInvariant.Readable
      ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))
    (scheduled : GeneralBorrowEvents.Scheduled
      ((location.perms.get index).getD node.defaultLocationState) .Read related) :
    ∃ recorded next delta,
      ((location.perms.get index).getD node.defaultLocationState).recordNewAccess .Read related = .Recorded recorded ∧
      recorded.performAccess .Read related (protections.contains node.tag) = .Success next delta ∧
      GeneralBorrowProtectedReadInvariant.Readable next (protections.contains node.tag) ∧
      (GeneralBorrowExposurePermissionUpdate.cacheUpdate tree location protections index node next).outcome = .ok () ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree
        (GeneralBorrowExposurePermissionUpdate.nextLocation tree location protections index node next) protections ∧
      (∀ query, GeneralBorrowExposureCardinality.counter
        (GeneralBorrowExposurePermissionUpdate.cacheUpdate tree location protections index node next).cache query .Read =
        GeneralBorrowExposureCardinality.counter location.exposedCache query .Read) := by
  obtain ⟨recorded,next,delta,record,access,good,support⟩ := visit _ related _ readable scheduled
  have preserved := GeneralBorrowExposurePermissionUpdate.preserves tree location protections depth coherent index node present next
  exact ⟨recorded,next,delta,record,access,good,preserved.1,preserved.2,
    fun query => update_read_counter tree location protections depth coherent index node present next support query⟩

end DuplicatePrefix.GeneralBorrowExposedNonleafRead
