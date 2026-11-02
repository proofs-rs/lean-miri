import duplicate_prefix.S05RetainedConeOwnership
import duplicate_prefix.S05LiveSubtreeCacheSoundness
import duplicate_prefix.GeneralBorrowStructuralHistoryState
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal

namespace DuplicatePrefix.S05RetainedConeNumericAdapter
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
open GeneralBorrowSifaPermissionConsistency S05LiveSubtreeCacheSoundness
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization S05WriteCacheContributorOwnership
set_option autoImplicit false
set_option maxHeartbeats 1500000

private theorem area_path {tree : BorrowTree} {root query target : UniIndex}
    (area : GeneralBorrowWildcardControlStack.Support tree root) (graph : Reciprocal tree)
    (inside : area.contains query) (path : Path tree query target) : area.contains target := by
  induction path with
  | refl node present => exact inside
  | @step parent child earlier node present edge ih =>
    obtain ⟨parentNode,parentPresent,member⟩ := graph child node present parent edge
    exact area.children parent parentNode ih parentPresent child member

/-- Existing local ownership makes each relevant exposed Write support path
live; no Disabled/Frozen shortcut is assumed to constrain inaccessible nodes. -/
private theorem live_of_write_fields (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex)
    (area : GeneralBorrowWildcardControlStack.Support tree root)
    (liveRights : ∀ query node, area.contains query → tree.nodes.get query = some node →
      ∀ witness witnessNode, tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      ((location.perms.get query).getD node.defaultLocationState).permission ≠ .Disabled ∧
      ((location.perms.get query).getD node.defaultLocationState).permission ≠ .Frozen)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree)
    (query witness : UniIndex) (witnessNode : TreeNode) (inside : area.contains query)
    (found : tree.nodes.get witness = some witnessNode) (exposed : witnessNode.isExposed = true)
    (supported : supports (effective location protections witness witnessNode) .Write = true) :
    LiveCone tree location query witness := by
  intro middle node present queryWalk witnessWalk
  have path := GeneralBorrowWildcardControlWitness.path_of_walk tree depth query middle node present _ queryWalk
  have middleInside := area_path area graph inside path
  have live := liveRights middle node middleInside present witness witnessNode found exposed witnessWalk supported
  exact live

theorem callback_live_of_ownership (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : S05RetainedConeOwnership.CallbackOwnership tree location protections root position maximum)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree)
    (query witness : UniIndex) (witnessNode : TreeNode) (inside : rights.area.contains query)
    (found : tree.nodes.get witness = some witnessNode) (exposed : witnessNode.isExposed = true)
    (supported : supports (effective location protections witness witnessNode) .Write = true) :
    LiveCone tree location query witness := by
  exact live_of_write_fields tree location protections root rights.area
    rights.liveRights depth graph query witness witnessNode inside found exposed supported

theorem generalized_live_of_ownership (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : S05RetainedConeOwnership.GeneralizedOwnership tree location protections root position maximum)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree)
    (query witness : UniIndex) (witnessNode : TreeNode) (inside : rights.area.contains query)
    (found : tree.nodes.get witness = some witnessNode) (exposed : witnessNode.isExposed = true)
    (supported : supports (effective location protections witness witnessNode) .Write = true) :
    LiveCone tree location query witness := by
  exact callback_live_of_ownership tree location protections root position maximum rights.toCallbackOwnership depth graph query witness witnessNode inside found exposed supported

theorem live_of_ownership (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : S05RetainedConeOwnership.Ownership tree location protections root position maximum)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree)
    (query witness : UniIndex) (witnessNode : TreeNode) (inside : rights.area.contains query)
    (found : tree.nodes.get witness = some witnessNode) (exposed : witnessNode.isExposed = true)
    (supported : supports (effective location protections witness witnessNode) .Write = true) :
    LiveCone tree location query witness := by
  exact callback_live_of_ownership tree location protections root position maximum rights.toCallbackOwnership
    depth graph query witness witnessNode inside found exposed supported

private theorem skipped_cache (state : LocationState) (notDisabled : state.permission ≠ .Disabled)
    (skipped : skip state .Write .ForeignAccess = true) : state.idempotentForeignAccess = .Write := by
  rcases state with ⟨permission,accessed,cache⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases cache <;>
      simp_all [skip,AccessRelatedness.isForeign,IdempotentForeignAccess.canSkipForeignAccess,
        IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
        IdempotentForeignAccess.rank,Permission.isDisabled,Permission.isFrozen]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases cache <;>
      simp_all [skip,AccessRelatedness.isForeign,IdempotentForeignAccess.canSkipForeignAccess,
        IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
        IdempotentForeignAccess.rank,Permission.isDisabled,Permission.isFrozen]

private theorem write_bound_retained (state : LocationState) (held : Bool)
    (bound : Consistent {state with idempotentForeignAccess := .Write} held) :
    losesWriteWhenForeign state.permission = false := by
  rcases state with ⟨permission,accessed,cache⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases held <;>
      simp_all [Consistent,Permission.strongestIdempotentForeignAccess,IdempotentForeignAccess.rank]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases held <;> simp_all [Consistent,Permission.strongestIdempotentForeignAccess,IdempotentForeignAccess.rank,losesWriteWhenForeign]

/-- Numeric live-cone cache soundness supplies the required SkipStable without
ordering descendant cached values. Raw local ownership justifies the live cone. -/
theorem skip_stable_of_write_fields (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (maximum : Option BorTag)
    (area : GeneralBorrowWildcardControlStack.Support tree root)
    (liveRights : ∀ query node, area.contains query → tree.nodes.get query = some node →
      ∀ witness witnessNode, tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      ((location.perms.get query).getD node.defaultLocationState).permission ≠ .Disabled ∧
      ((location.perms.get query).getD node.defaultLocationState).permission ≠ .Frozen)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree)
    (sound : Soundness tree location protections area.contains) :
    SkipStable tree location protections maximum area.contains := by
  intro query node inside present skipped witness witnessNode found exposed walked supported
  have liveAt := liveRights query node inside present witness witnessNode found exposed walked supported
  have cache := skipped_cache _ liveAt.1 skipped
  have live := live_of_write_fields tree location protections root area liveRights depth graph query witness witnessNode inside found exposed supported
  have bound := sound query node inside present witness witnessNode found walked live
  rw [cache] at bound
  have retained := write_bound_retained _ (protections.contains witnessNode.tag) bound
  simp only [removable,retained,Bool.and_false]

theorem callback_skip_stable (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : S05RetainedConeOwnership.CallbackOwnership tree location protections root position maximum)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree)
    (sound : Soundness tree location protections rights.area.contains) :
    SkipStable tree location protections maximum rights.area.contains := by
  exact skip_stable_of_write_fields tree location protections root maximum rights.area
    rights.liveRights depth graph sound

theorem generalized_skip_stable (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : S05RetainedConeOwnership.GeneralizedOwnership tree location protections root position maximum)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree)
    (sound : Soundness tree location protections rights.area.contains) :
    SkipStable tree location protections maximum rights.area.contains := by
  exact callback_skip_stable tree location protections root position maximum rights.toCallbackOwnership depth graph sound

theorem skip_stable (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (rights : S05RetainedConeOwnership.Ownership tree location protections root position maximum)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (graph : Reciprocal tree)
    (sound : Soundness tree location protections rights.area.contains) :
    SkipStable tree location protections maximum rights.area.contains := by
  exact callback_skip_stable tree location protections root position maximum rights.toCallbackOwnership depth graph sound

/-- Canonical fieldless formation of the existing Row: only Write ancestry
and numeric live-cone Soundness are supplied. SkipStable and protector Read
are derived; selected-root cutoff and normal permissions remain unchanged. -/
theorem row_of_write_fields (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (graph : Reciprocal tree) (tagOrder : ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (wildcard : source = none → selectedRoot = none)
    (rootPath : ∀ anchor, source = some anchor →
      ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
        selectedRoot.map UniIndex.toNat)
    (rootPresent : ∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node)
    (cutoff : maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag))
    (normal : ∀ anchor, source = some anchor →
      ∃ component : GeneralBorrowExposedScopedNormal.Component
          (source_normal_projection tree default protections).topology anchor.toNat,
        ∀ index, component.support index → index < tree.nodes.data.size →
          ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
            DuplicatePrefixScalarAuthorization.Compatible state .Write
              (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
              ((source_normal_projection tree location protections).protectedNodes.contains index))
    (ownership : ∀ position, (valid : position < tree.roots.size) →
      selectedRoot ≠ some tree.roots[position] →
      ∃ area : GeneralBorrowWildcardControlStack.Support tree tree.roots[position],
        (∀ query, area.contains query → Covers tree.nodes tree.roots[position] query) ∧
        (∀ query node, area.contains query → tree.nodes.get query = some node →
      ((location.perms.get query).getD node.defaultLocationState).possible = true) ∧
        (∀ query node, area.contains query → tree.nodes.get query = some node →
      (aboveMaximum node maximum = true ∨ ¬ S05RetainedConeOwnership.RetainedBelow tree location protections maximum query) →
      DuplicatePrefixScalarAuthorization.Compatible
        ((location.perms.get query).getD node.defaultLocationState) .Write .ForeignAccess (protections.contains node.tag)) ∧
        (position = 0 → ∀ query node, area.contains query → tree.nodes.get query = some node →
      ∀ witness witnessNode, tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      DuplicatePrefixScalarAuthorization.Compatible
        ((location.perms.get query).getD node.defaultLocationState) .Write .LocalAccess (protections.contains node.tag)) ∧
        S05CutoffOwnershipGeometry.CutoffWitness tree location protections tree.roots[position] position maximum area.contains ∧
        (∀ query node, area.contains query → tree.nodes.get query = some node →
      ∀ witness witnessNode, tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      ((location.perms.get query).getD node.defaultLocationState).permission ≠ .Disabled ∧
      ((location.perms.get query).getD node.defaultLocationState).permission ≠ .Frozen) ∧
        Soundness tree location protections area.contains) :
    DuplicatePrefixBorrowAuthorization.Row tree location protections source selectedRoot maximum := by
  apply S05RetainedConeOwnership.row_of_write_fields tree location protections source selectedRoot maximum
    depth tagOrder coherent short wildcard rootPath rootPresent cutoff normal
  intro position valid other
  obtain ⟨area,covers,possible,foreign,primaryWrite,witness,liveRights,sound⟩ := ownership position valid other
  exact ⟨area,covers,possible,foreign,primaryWrite,witness,
    skip_stable_of_write_fields tree location protections _ maximum area liveRights depth graph sound⟩

theorem callback_row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (graph : Reciprocal tree) (tagOrder : ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (wildcard : source = none → selectedRoot = none)
    (rootPath : ∀ anchor, source = some anchor →
      ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
        selectedRoot.map UniIndex.toNat)
    (rootPresent : ∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node)
    (cutoff : maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag))
    (normal : ∀ anchor, source = some anchor →
      ∃ component : GeneralBorrowExposedScopedNormal.Component
          (source_normal_projection tree default protections).topology anchor.toNat,
        ∀ index, component.support index → index < tree.nodes.data.size →
          ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
            DuplicatePrefixScalarAuthorization.Compatible state .Write
              (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
              ((source_normal_projection tree location protections).protectedNodes.contains index))
    (ownership : ∀ position, (valid : position < tree.roots.size) →
      selectedRoot ≠ some tree.roots[position] →
      ∃ rights : S05RetainedConeOwnership.CallbackOwnership tree location protections tree.roots[position] position maximum,
        S05LiveSubtreeCacheSoundness.Soundness tree location protections rights.area.contains) :
    DuplicatePrefixBorrowAuthorization.Row tree location protections source selectedRoot maximum := by
  apply row_of_write_fields tree location protections source selectedRoot maximum depth graph tagOrder coherent short
    wildcard rootPath rootPresent cutoff normal
  intro position valid other
  obtain ⟨rights,sound⟩ := ownership position valid other
  exact ⟨rights.area,rights.covers,rights.possible,rights.foreign,
    (fun primary query node inside present witness witnessNode found exposed walked supported =>
      rights.primaryLocal primary query node inside present witness witnessNode found exposed walked .Write supported),
    rights.cutoff,rights.liveRights,sound⟩

theorem generalized_row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (graph : Reciprocal tree) (tagOrder : ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (wildcard : source = none → selectedRoot = none)
    (rootPath : ∀ anchor, source = some anchor →
      ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
        selectedRoot.map UniIndex.toNat)
    (rootPresent : ∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node)
    (cutoff : maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag))
    (normal : ∀ anchor, source = some anchor →
      ∃ component : GeneralBorrowExposedScopedNormal.Component
          (source_normal_projection tree default protections).topology anchor.toNat,
        ∀ index, component.support index → index < tree.nodes.data.size →
          ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
            DuplicatePrefixScalarAuthorization.Compatible state .Write
              (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
              ((source_normal_projection tree location protections).protectedNodes.contains index))
    (ownership : ∀ position, (valid : position < tree.roots.size) →
      selectedRoot ≠ some tree.roots[position] →
      ∃ rights : S05RetainedConeOwnership.GeneralizedOwnership tree location protections tree.roots[position] position maximum,
        S05LiveSubtreeCacheSoundness.Soundness tree location protections rights.area.contains) :
    DuplicatePrefixBorrowAuthorization.Row tree location protections source selectedRoot maximum := by
  apply callback_row tree location protections source selectedRoot maximum depth graph tagOrder coherent short
    wildcard rootPath rootPresent cutoff normal
  intro position valid other
  obtain ⟨rights,sound⟩ := ownership position valid other
  exact ⟨rights.toCallbackOwnership,sound⟩

theorem row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (graph : Reciprocal tree) (tagOrder : ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (wildcard : source = none → selectedRoot = none)
    (rootPath : ∀ anchor, source = some anchor →
      ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
        selectedRoot.map UniIndex.toNat)
    (rootPresent : ∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node)
    (cutoff : maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag))
    (normal : ∀ anchor, source = some anchor →
      ∃ component : GeneralBorrowExposedScopedNormal.Component
          (source_normal_projection tree default protections).topology anchor.toNat,
        ∀ index, component.support index → index < tree.nodes.data.size →
          ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
            DuplicatePrefixScalarAuthorization.Compatible state .Write
              (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
              ((source_normal_projection tree location protections).protectedNodes.contains index))
    (ownership : ∀ position, (valid : position < tree.roots.size) →
      selectedRoot ≠ some tree.roots[position] →
      ∃ rights : S05RetainedConeOwnership.Ownership tree location protections tree.roots[position] position maximum,
        S05LiveSubtreeCacheSoundness.Soundness tree location protections rights.area.contains) :
    DuplicatePrefixBorrowAuthorization.Row tree location protections source selectedRoot maximum := by
  apply callback_row tree location protections source selectedRoot maximum depth graph tagOrder coherent short
    wildcard rootPath rootPresent cutoff normal
  intro position valid other
  obtain ⟨rights,sound⟩ := ownership position valid other
  exact ⟨rights.toCallbackOwnership,sound⟩

/-- Initial metadata and permission-table facts for one physical partition.
This packet assumes neither callback authorization nor a completed borrow row.
Its necessity for ordinary valid calls is a separate coverage obligation. -/
structure Snapshot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag) where
  wildcard : source = none → selectedRoot = none
  rootPath : ∀ anchor, source = some anchor →
      ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
        selectedRoot.map UniIndex.toNat
  rootPresent : ∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node
  cutoff : maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag)
  normal : ∀ anchor, source = some anchor →
      ∃ component : GeneralBorrowExposedScopedNormal.Component
          (source_normal_projection tree default protections).topology anchor.toNat,
        ∀ index, component.support index → index < tree.nodes.data.size →
          ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
            DuplicatePrefixScalarAuthorization.Compatible state .Write
              (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
              ((source_normal_projection tree location protections).protectedNodes.contains index)
  ownership : ∀ position, (valid : position < tree.roots.size) →
      selectedRoot ≠ some tree.roots[position] →
      ∃ rights : S05RetainedConeOwnership.Ownership tree location protections tree.roots[position] position maximum,
        S05LiveSubtreeCacheSoundness.Soundness tree location protections rights.area.contains

/-- Count-independent raw snapshot for generalized callback ownership. -/
structure GeneralizedSnapshot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag) where
  wildcard : source = none → selectedRoot = none
  rootPath : ∀ anchor, source = some anchor →
      ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
        selectedRoot.map UniIndex.toNat
  rootPresent : ∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node
  cutoff : maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag)
  normal : ∀ anchor, source = some anchor →
      ∃ component : GeneralBorrowExposedScopedNormal.Component
          (source_normal_projection tree default protections).topology anchor.toNat,
        ∀ index, component.support index → index < tree.nodes.data.size →
          ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
            DuplicatePrefixScalarAuthorization.Compatible state .Write
              (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
              ((source_normal_projection tree location protections).protectedNodes.contains index)
  ownership : ∀ position, (valid : position < tree.roots.size) →
      selectedRoot ≠ some tree.roots[position] →
      ∃ rights : S05RetainedConeOwnership.GeneralizedOwnership tree location protections tree.roots[position] position maximum,
        S05LiveSubtreeCacheSoundness.Soundness tree location protections rights.area.contains


/-- Canonical snapshot with no virtual Read ancestry requirement. -/
structure CallbackSnapshot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag) where
  wildcard : source = none → selectedRoot = none
  rootPath : ∀ anchor, source = some anchor →
      ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
        selectedRoot.map UniIndex.toNat
  rootPresent : ∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node
  cutoff : maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag)
  normal : ∀ anchor, source = some anchor →
      ∃ component : GeneralBorrowExposedScopedNormal.Component
          (source_normal_projection tree default protections).topology anchor.toNat,
        ∀ index, component.support index → index < tree.nodes.data.size →
          ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
            DuplicatePrefixScalarAuthorization.Compatible state .Write
              (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
              ((source_normal_projection tree location protections).protectedNodes.contains index)
  ownership : ∀ position, (valid : position < tree.roots.size) →
      selectedRoot ≠ some tree.roots[position] →
      ∃ rights : S05RetainedConeOwnership.CallbackOwnership tree location protections tree.roots[position] position maximum,
        S05LiveSubtreeCacheSoundness.Soundness tree location protections rights.area.contains


theorem Snapshot.toCallbackSnapshot {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {source selectedRoot : Option UniIndex} {maximum : Option BorTag}
    (snapshot : Snapshot tree location protections source selectedRoot maximum) :
    CallbackSnapshot tree location protections source selectedRoot maximum := {
  wildcard := snapshot.wildcard, rootPath := snapshot.rootPath,
  rootPresent := snapshot.rootPresent, cutoff := snapshot.cutoff, normal := snapshot.normal,
  ownership := by
    intro position valid different
    obtain ⟨rights,sound⟩ := snapshot.ownership position valid different
    exact ⟨rights.toCallbackOwnership,sound⟩ }

theorem GeneralizedSnapshot.toCallbackSnapshot {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {source selectedRoot : Option UniIndex} {maximum : Option BorTag}
    (snapshot : GeneralizedSnapshot tree location protections source selectedRoot maximum) :
    CallbackSnapshot tree location protections source selectedRoot maximum := {
  wildcard := snapshot.wildcard, rootPath := snapshot.rootPath,
  rootPresent := snapshot.rootPresent, cutoff := snapshot.cutoff, normal := snapshot.normal,
  ownership := by
    intro position valid different
    obtain ⟨rights,sound⟩ := snapshot.ownership position valid different
    exact ⟨rights.toCallbackOwnership,sound⟩ }

/-- Preserve existing snapshot callers while relaxing only virtual Local rights. -/
theorem Snapshot.generalize {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {source selectedRoot : Option UniIndex} {maximum : Option BorTag}
    (snapshot : Snapshot tree location protections source selectedRoot maximum) :
    GeneralizedSnapshot tree location protections source selectedRoot maximum := {
  wildcard := snapshot.wildcard, rootPath := snapshot.rootPath,
  rootPresent := snapshot.rootPresent, cutoff := snapshot.cutoff, normal := snapshot.normal,
  ownership := by
    intro position valid different
    obtain ⟨rights,sound⟩ := snapshot.ownership position valid different
    exact ⟨rights.generalize,sound⟩ }

/-- Count-independent Positive from anonymous per-window Write data. No new
ownership/Snapshot variant or primary Read ancestry is required. GraphState,
tag order, numeric cache soundness and cutoff metadata remain explicit.
No operation result or ordinary-validity equivalence is asserted. -/
theorem positive_of_write_fields (tree : BorrowTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (tagOrder : ParentTagOrder tree) (short : tree.nodes.size < 65536)
    (positiveLength : 0 < len.toNat)
    (bounds : offset.toNat + len.toNat ≤ tree.locations.size.bytes.toNat)
    (sourcePresent : ∀ anchor, source = some anchor → ∃ node, tree.nodeAt anchor = some node)
    (wildcardRoot : source = none → 0 < tree.roots.size)
    (snapshots : GeneralRangeMapOrigins.OwnedOn
      (fun location => (source = none → selectedRoot = none) ∧
        (∀ anchor, source = some anchor →
          ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
            selectedRoot.map UniIndex.toNat) ∧
        (∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node) ∧
        maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag) ∧
        (∀ anchor, source = some anchor →
          ∃ component : GeneralBorrowExposedScopedNormal.Component
              (source_normal_projection tree default protections).topology anchor.toNat,
            ∀ index, component.support index → index < tree.nodes.data.size →
              ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
                DuplicatePrefixScalarAuthorization.Compatible state .Write
                  (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
                  ((source_normal_projection tree location protections).protectedNodes.contains index)) ∧
        (∀ position, (valid : position < tree.roots.size) →
      selectedRoot ≠ some tree.roots[position] →
      ∃ area : GeneralBorrowWildcardControlStack.Support tree tree.roots[position],
        (∀ query, area.contains query → Covers tree.nodes tree.roots[position] query) ∧
        (∀ query node, area.contains query → tree.nodes.get query = some node →
      ((location.perms.get query).getD node.defaultLocationState).possible = true) ∧
        (∀ query node, area.contains query → tree.nodes.get query = some node →
      (aboveMaximum node maximum = true ∨ ¬ S05RetainedConeOwnership.RetainedBelow tree location protections maximum query) →
      DuplicatePrefixScalarAuthorization.Compatible
        ((location.perms.get query).getD node.defaultLocationState) .Write .ForeignAccess (protections.contains node.tag)) ∧
        (position = 0 → ∀ query node, area.contains query → tree.nodes.get query = some node →
      ∀ witness witnessNode, tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      DuplicatePrefixScalarAuthorization.Compatible
        ((location.perms.get query).getD node.defaultLocationState) .Write .LocalAccess (protections.contains node.tag)) ∧
        S05CutoffOwnershipGeometry.CutoffWitness tree location protections tree.roots[position] position maximum area.contains ∧
        (∀ query node, area.contains query → tree.nodes.get query = some node →
      ∀ witness witnessNode, tree.nodes.get witness = some witnessNode → witnessNode.isExposed = true →
      query ∈ walk tree.nodes (tree.nodes.size+1) witness →
      supports (effective location protections witness witnessNode) .Write = true →
      ((location.perms.get query).getD node.defaultLocationState).permission ≠ .Disabled ∧
      ((location.perms.get query).getD node.defaultLocationState).permission ≠ .Frozen) ∧
        Soundness tree location protections area.contains))
      offset (offset + len) tree.locations)
    (coherent : GeneralRangeMapOrigins.OwnedOn
      (fun location => GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
      offset (offset + len) tree.locations) :
    DuplicatePrefixBorrowAuthorization.Positive tree protections source selectedRoot maximum offset len := by
  obtain ⟨depth⟩ := graph.depth
  refine { positive := positiveLength, bounds := bounds, sourcePresent := sourcePresent,
           wildcardRoot := wildcardRoot, rows := ?_ }
  intro position valid nonempty start stop
  obtain ⟨wildcard,rootPath,rootPresent,cutoff,normal,ownership⟩ := snapshots position valid nonempty start stop
  have forest := Classical.choice (graph.forest tree.locations.entries[position].data protections)
  have reciprocal := GeneralBorrowExposedScopedReciprocal.of_forest tree _ protections forest depth
  exact ⟨row_of_write_fields tree _ protections source selectedRoot maximum
    depth reciprocal tagOrder (coherent position valid nonempty start stop) short
    wildcard rootPath rootPresent cutoff normal ownership⟩

theorem callback_positive (tree : BorrowTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (tagOrder : ParentTagOrder tree) (short : tree.nodes.size < 65536)
    (positiveLength : 0 < len.toNat)
    (bounds : offset.toNat + len.toNat ≤ tree.locations.size.bytes.toNat)
    (sourcePresent : ∀ anchor, source = some anchor → ∃ node, tree.nodeAt anchor = some node)
    (wildcardRoot : source = none → 0 < tree.roots.size)
    (snapshots : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (CallbackSnapshot tree location protections source selectedRoot maximum))
      offset (offset + len) tree.locations)
    (coherent : GeneralRangeMapOrigins.OwnedOn
      (fun location => GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
      offset (offset + len) tree.locations) :
    DuplicatePrefixBorrowAuthorization.Positive tree protections source selectedRoot maximum offset len := by
  apply positive_of_write_fields tree protections source selectedRoot maximum offset len
    graph tagOrder short positiveLength bounds sourcePresent wildcardRoot (coherent := coherent)
  intro position valid nonempty start stop
  obtain ⟨snapshot⟩ := snapshots position valid nonempty start stop
  refine ⟨snapshot.wildcard,snapshot.rootPath,snapshot.rootPresent,snapshot.cutoff,snapshot.normal,?_⟩
  intro rootPosition rootValid other
  obtain ⟨rights,sound⟩ := snapshot.ownership rootPosition rootValid other
  exact ⟨rights.area,rights.covers,rights.possible,rights.foreign,
    (fun primary query node inside present witness witnessNode found exposed walked supported =>
      rights.primaryLocal primary query node inside present witness witnessNode found exposed walked .Write supported),
    rights.cutoff,rights.liveRights,sound⟩

theorem generalized_positive (tree : BorrowTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (tagOrder : ParentTagOrder tree) (short : tree.nodes.size < 65536)
    (positiveLength : 0 < len.toNat)
    (bounds : offset.toNat + len.toNat ≤ tree.locations.size.bytes.toNat)
    (sourcePresent : ∀ anchor, source = some anchor → ∃ node, tree.nodeAt anchor = some node)
    (wildcardRoot : source = none → 0 < tree.roots.size)
    (snapshots : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralizedSnapshot tree location protections source selectedRoot maximum))
      offset (offset + len) tree.locations)
    (coherent : GeneralRangeMapOrigins.OwnedOn
      (fun location => GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
      offset (offset + len) tree.locations) :
    DuplicatePrefixBorrowAuthorization.Positive tree protections source selectedRoot maximum offset len := by
  apply callback_positive tree protections source selectedRoot maximum offset len graph tagOrder short
    positiveLength bounds sourcePresent wildcardRoot ?_ coherent
  intro position valid nonempty start stop
  obtain ⟨snapshot⟩ := snapshots position valid nonempty start stop
  exact ⟨snapshot.toCallbackSnapshot⟩

theorem positive (tree : BorrowTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (tagOrder : ParentTagOrder tree) (short : tree.nodes.size < 65536)
    (positiveLength : 0 < len.toNat)
    (bounds : offset.toNat + len.toNat ≤ tree.locations.size.bytes.toNat)
    (sourcePresent : ∀ anchor, source = some anchor → ∃ node, tree.nodeAt anchor = some node)
    (wildcardRoot : source = none → 0 < tree.roots.size)
    (snapshots : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Snapshot tree location protections source selectedRoot maximum))
      offset (offset + len) tree.locations)
    (coherent : GeneralRangeMapOrigins.OwnedOn
      (fun location => GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
      offset (offset + len) tree.locations) :
    DuplicatePrefixBorrowAuthorization.Positive tree protections source selectedRoot maximum offset len := by
  apply callback_positive tree protections source selectedRoot maximum offset len graph tagOrder short
    positiveLength bounds sourcePresent wildcardRoot ?_ coherent
  intro position valid nonempty start stop
  obtain ⟨snapshot⟩ := snapshots position valid nonempty start stop
  exact ⟨snapshot.toCallbackSnapshot⟩


end DuplicatePrefix.S05RetainedConeNumericAdapter
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05RetainedConeNumericAdapter." then
      for ax in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
          throwError "unapproved axiom {ax}"
