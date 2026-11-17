import duplicate_prefix.GeneralBorrowExposedConditionalWritePermissions
namespace DuplicatePrefix.GeneralBorrowExposedConditionalAccessSupport
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Initial coherent counters prohibit an exposed node from supporting an
access whose selected-kind self counter is zero. No classification is assumed. -/
theorem exposed_zero (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (exposed : node.isExposed = true)
    (kind : AccessKind) (zero : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index kind = 0) :
    GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective location protections index node) kind = false := by
  cases supported : GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective location protections index node) kind with
  | false => rfl
  | true =>
    have positive := GeneralBorrowExposureCardinality.exposed_self location.exposedCache tree.nodes
      (GeneralBorrowExposureCardinality.effective location protections) coherent short index node present exposed kind supported
    have positiveCount : 0 < GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index kind := by cases kind <;> exact positive
    omega

/-- An exposed zero-Read row is Disabled, so any successful foreign Read keeps
its entire permission level. This is the scalar basis for exact cache framing. -/
theorem read_zero_permission (state : LocationState) (held : Bool)
    (zero : GeneralBorrowExposureCardinality.supports (state.permission.strongestAllowedLocalAccess held) .Read = false) :
    state.permission = .Disabled := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases held <;> simp_all [GeneralBorrowExposureCardinality.supports,Permission.strongestAllowedLocalAccess,GeneralBorrowExposureAncestorFold.supportsRead]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases held <;> simp_all [GeneralBorrowExposureCardinality.supports,Permission.strongestAllowedLocalAccess,GeneralBorrowExposureAncestorFold.supportsRead]

/-- A legal local Read leaves both local exposure strengths unchanged. -/
theorem local_read_levels (state : LocationState) (held : Bool)
    (compatible : GeneralBorrowProtectedReadCompatible.Compatible state .LocalAccess held) :
    ∃ next delta, state.performAccess .Read .LocalAccess held = .Success next delta ∧
      next.permission = state.permission := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases accessed <;> cases sifa <;> cases held <;>
      simp [GeneralBorrowProtectedReadCompatible.Compatible,LocationState.possible,Permission.isUnique] at compatible <;> exact ⟨_,_,rfl,rfl⟩
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases accessed <;> cases sifa <;> cases held <;>
      simp [GeneralBorrowProtectedReadCompatible.Compatible,LocationState.possible,Permission.isUnique] at compatible <;> exact ⟨_,_,rfl,rfl⟩
theorem exposed_descendant (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (kind : AccessKind) (root witness : UniIndex) (node : TreeNode)
    (present : tree.nodes.get witness = some node) (exposed : node.isExposed = true)
    (supported : GeneralBorrowExposureCardinality.supports
      (GeneralBorrowExposureCardinality.effective location protections witness node) kind = true)
    (ancestor : root ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) witness) :
    0 < (GeneralBorrowExposureCardinality.counter location.exposedCache root kind).toNat := by
  rw [GeneralBorrowExposureCardinality.nat_exact location.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective location protections) coherent short root kind]
  apply List.length_pos_iff.mpr
  intro absent
  have member : (witness,node) ∈ tree.nodes.entries.toList.filter
      (GeneralBorrowExposureCardinality.contributes tree.nodes
        (GeneralBorrowExposureCardinality.effective location protections) root kind) := by
    refine List.mem_filter.mpr ⟨(GeneralBorrowFreshReuseProtection.entries_get tree.nodes witness node).mpr present,?_⟩
    simp only [GeneralBorrowExposureCardinality.contributes,exposed,supported,Bool.true_and]
    exact List.contains_iff_mem.mpr ancestor
  rw [absent] at member
  cases member


end DuplicatePrefix.GeneralBorrowExposedConditionalAccessSupport
