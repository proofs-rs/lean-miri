import duplicate_prefix.GeneralBorrowRootOnlyNormalCache
import duplicate_prefix.GeneralBorrowExposedScopedNormalExposure
import duplicate_prefix.GeneralBorrowExposedScopedNormalCache
namespace DuplicatePrefix.GeneralBorrowExposedScopedAncestorNormal
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Exposed nodes in the accessed component may be arbitrary ancestors, rather
than requiring the component to be hidden or its root to be the only exposed
node. Their initial Unique permission makes every actual local cache event a
source no-op. Other components may contain arbitrary exposed nodes. -/
theorem cache (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology anchor.toNat)
    (owned : GeneralBorrowExposedScopedNormal.Owned (source_normal_projection tree location protections) anchor.toNat kind component)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (profile : ∀ index node state, component.support index.toNat → tree.nodeAt index = some node →
      node.isExposed = true → tree.locationStateAt location index = some state →
      index.toNat ∈ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat ∧
      state.permission = .Unique) :
    (tree.performNormalAccessAt location anchor kind protections mode).location.exposedCache = location.exposedCache := by
  let projection := source_normal_projection tree location protections
  let schedule := projection.topology.traverse anchor.toNat mode (sourceNormalSkipped projection kind)
  have geometry := GeneralBorrowExposedScopedNormalMetadata.valid_aligned tree location protections anchor anchorNode anchorPresent
  have completed := GeneralBorrowExposedScopedNormal.normal projection anchor.toNat kind mode forest geometry.1 geometry.2 component owned
  have visited := GeneralBorrowStorage.events_visited schedule.2 schedule.1 kind projection completed
  change (projection.performAccess anchor.toNat kind mode).visited = schedule.2 at visited
  apply GeneralBorrowRootOnlyNormalCache.event_noop_cache
  intro event member index node state converted present exposed old
  have scheduled : event ∈ schedule.2 := by rw [←visited];exact member
  have inside := GeneralBorrowPresence.traversal_present projection.topology component.support component.parents component.children
    anchor.toNat component.anchor mode (sourceNormalSkipped projection kind) event scheduled
  have same : index.toNat = event.node := by
    unfold UniIndex.ofNat? at converted
    split at converted
    · have equal := Option.some.inj converted
      rw [←equal]
      dsimp only [UniIndex.toNat]
      rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega)]
    · cases converted
  rw [←same] at inside
  obtain ⟨ancestor,unique⟩ := profile index node state inside present exposed old
  change index.toNat ∈ projection.topology.ancestorPath anchor.toNat at ancestor
  have relation := (GeneralBorrowTraversal.traversal_data projection.topology forest anchor.toNat geometry.1
    mode (sourceNormalSkipped projection kind)).2 event scheduled
  have localEvent : event.relatedness = .LocalAccess := by
    simpa only [←same,ite_eq_left ancestor] using relation.2
  rw [unique,localEvent]
  exact GeneralBorrowRootOnlyNormalCache.unique_local_noop kind _

/-- The initial ancestor profile yields real normal completion, exact exposed
cache, coherence, and an exact stored-permission frame on other components. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology anchor.toNat)
    (owned : GeneralBorrowExposedScopedNormal.Owned (source_normal_projection tree location protections) anchor.toNat kind component)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (profile : ∀ index node state, component.support index.toNat → tree.nodeAt index = some node →
      node.isExposed = true → tree.locationStateAt location index = some state →
      index.toNat ∈ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat ∧
      state.permission = .Unique)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections) :
    (tree.performNormalAccessAt location anchor kind protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor kind protections mode).outcome = .ok () ∧
    (tree.performNormalAccessAt location anchor kind protections mode).location.exposedCache = location.exposedCache ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree (tree.performNormalAccessAt location anchor kind protections mode).location protections ∧
    (∀ query node, tree.nodeAt query = some node → ¬component.support query.toNat →
      (tree.performNormalAccessAt location anchor kind protections mode).location.perms.get query = location.perms.get query) := by
  have result := GeneralBorrowExposedScopedNormalExposure.access tree location protections anchor kind mode depth children anchorNode anchorPresent forest component owned coherent
  exact ⟨result.1,result.2.1,cache tree location protections anchor kind mode forest component owned anchorNode anchorPresent profile,result.2.2,
    fun query node present outside => GeneralBorrowExposedScopedNormalCache.outside tree location protections anchor kind mode component query node present outside⟩
end DuplicatePrefix.GeneralBorrowExposedScopedAncestorNormal
