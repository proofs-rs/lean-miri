import duplicate_prefix.GeneralBorrowExposedScopedNormal
import duplicate_prefix.GeneralBorrowTwoRootNormalAccess
import duplicate_prefix.GeneralBorrowExposureCardinality
namespace DuplicatePrefix.GeneralBorrowExposedScopedNormalCache
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowExposedScopedNormal DuplicatePrefix.GeneralBorrowEvents
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Component separation yields exact stored permission frames outside the
selected component on every normal-access outcome, before any legality proof. -/
theorem outside (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (component : Component (source_normal_projection tree location protections).topology anchor.toNat)
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node)
    (notMember : ¬component.support query.toNat) :
    (tree.performNormalAccessAt location anchor kind protections mode).location.perms.get query = location.perms.get query := by
  apply GeneralBorrowTwoRootNormalAccess.normal_unvisited tree location protections anchor query node kind mode present
  intro event member equal
  have inside := GeneralBorrowPresence.traversal_present _ component.support component.parents component.children anchor.toNat
    component.anchor mode (sourceNormalSkipped (source_normal_projection tree location protections) kind) event member
  rw [equal] at inside
  exact notMember inside

/-- Hidden selected components retain exact cache rows and full global
exposure-cardinality coherence. Exposed references and protected permissions
outside the component are unrestricted; they are proved unvisited. No visitor
schedule, operation completion or poststate coherence is an input. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (component : Component (source_normal_projection tree location protections).topology anchor.toNat)
    (owned : Owned (source_normal_projection tree location protections) anchor.toNat kind component)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (hidden : ∀ index node,component.support index.toNat → tree.nodeAt index = some node → node.isExposed = false)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections) :
    (tree.performNormalAccessAt location anchor kind protections mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location anchor kind protections mode).outcome = .ok () ∧
    (tree.performNormalAccessAt location anchor kind protections mode).location.exposedCache = location.exposedCache ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree (tree.performNormalAccessAt location anchor kind protections mode).location protections ∧
    (∀ query node, tree.nodeAt query = some node → ¬component.support query.toNat →
      (tree.performNormalAccessAt location anchor kind protections mode).location.perms.get query = location.perms.get query) := by
  let projection := source_normal_projection tree location protections
  let schedule := projection.topology.traverse anchor.toNat mode (sourceNormalSkipped projection kind)
  have succeeded := GeneralBorrowExposedScopedNormal.access tree location protections anchor kind mode forest component owned depth children anchorNode anchorPresent
  have visited := GeneralBorrowStorage.events_visited schedule.2 schedule.1 kind projection succeeded.1
  change (projection.performAccess anchor.toNat kind mode).visited = schedule.2 at visited
  have confined := GeneralBorrowPresence.traversal_present projection.topology component.support component.parents component.children
    anchor.toNat component.anchor mode (sourceNormalSkipped projection kind)
  have unexposed : ∀ event ∈ (projection.performAccess anchor.toNat kind mode).visited,∀ index node,
      UniIndex.ofNat? event.node = some index → tree.nodeAt index = some node → node.isExposed = false := by
    intro event member index node converted present
    have scheduled : event ∈ schedule.2 := by rw [←visited];exact member
    have inside := confined event scheduled
    have same : index.toNat = event.node := by
      unfold UniIndex.ofNat? at converted
      split at converted
      · have equal := Option.some.inj converted
        rw [←equal]
        dsimp only [UniIndex.toNat]
        rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega)]
      · cases converted
    rw [←same] at inside
    exact hidden index node inside present
  have cache := GeneralBorrowNormalEventCacheFrame.normal_cache tree location anchor kind protections mode unexposed
  refine ⟨succeeded.1,succeeded.2,cache,?_,fun query node present notMember => outside tree location protections anchor kind mode component query node present notMember⟩
  intro query accessKind
  rw [cache,coherent query accessKind]
  unfold GeneralBorrowExposureCardinality.cardinality
  apply congrArg UInt16.ofNat
  apply congrArg List.length
  apply List.filter_congr
  intro row member
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
  by_cases inside : component.support row.1.toNat
  · have flag := hidden row.1 row.2 inside present
    simp only [GeneralBorrowExposureCardinality.contributes,flag,Bool.false_and]
  · have stored := outside tree location protections anchor kind mode component row.1 row.2 present inside
    simp only [GeneralBorrowExposureCardinality.contributes,GeneralBorrowExposureCardinality.effective,stored]
end DuplicatePrefix.GeneralBorrowExposedScopedNormalCache
