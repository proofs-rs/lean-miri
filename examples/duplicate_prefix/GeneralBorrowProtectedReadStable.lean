import duplicate_prefix.GeneralBorrowProtectedVirtualReadCache
import duplicate_prefix.GeneralBorrowProtectedReadSingleRoot
namespace DuplicatePrefix.GeneralBorrowProtectedReadStable
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.BorrowRangeAccess
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralBorrowEvents
open DuplicatePrefix.GeneralBorrowProtectedVirtualReadCache (StablePermission)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Every exposed node already has a permission stable under any source Read.
Unexposed nodes may still hold ordinary unconflicted reservations. -/
def AllExposed (tree : BorrowTree) (location : LocationTree) : Prop :=
  ∀ index node,tree.nodeAt index = some node → node.isExposed = true →
    StablePermission ((location.perms.get index).getD node.defaultLocationState).permission

private theorem transition (permission : Permission) (stable : StablePermission permission)
    (related : AccessRelatedness) (held : Bool) :
    performAccessTransition .Read related permission held = .Transition ⟨permission,permission⟩ := by
  rcases stable with reserved | frozen | cell
  · rw [reserved];cases related <;> cases held <;> rfl
  · rw [frozen];cases related <;> cases held <;> rfl
  · rw [cell];cases related <;> cases held <;> rfl

/-- Any present Read-stable query retains its effective permission through the
actual normal visitor and materialized writeback. Relatedness and visitation
are derived; no successful source operation is an input. -/
theorem normal_permission (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode) (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (initial : GeneralBorrowProtectedReadInvariant.Data (source_normal_projection tree location protections))
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node)
    (stable : StablePermission ((location.perms.get query).getD node.defaultLocationState).permission) :
    (((tree.performNormalAccessAt location anchor .Read protections mode).location.perms.get query).getD node.defaultLocationState).permission =
      ((location.perms.get query).getD node.defaultLocationState).permission := by
  let normal := source_normal_projection tree location protections
  have metadata := GeneralBorrowProtectedReadPermissionMetadata.metadata tree location protections anchor mode forest initial depth children anchorNode anchorPresent
  by_cases visited : query.toNat ∈ (normal.performAccess anchor.toNat .Read mode).visited.map TraversalEvent.node
  · obtain ⟨event,member,position⟩ := List.mem_map.mp visited
    obtain ⟨facts⟩ := metadata.2 event member
    have index : facts.index = query := by
      have converted := facts.converted
      rw [position] at converted
      exact Option.some.inj (converted.symm.trans (index_self query))
    have value : facts.node = node := by
      have found := facts.present
      rw [index] at found
      exact Option.some.inj (found.symm.trans present)
    have old : facts.oldState = (location.perms.get query).getD node.defaultLocationState := by
      have stored := facts.oldPresent
      rw [index] at stored
      simpa [BorrowTree.locationStateAt,present] using stored.symm
    have expected := transition facts.oldState.permission (by rw [old];exact stable) event.relatedness (protections.contains facts.node.tag)
    have same := PermTransitionOutcome.Transition.inj (facts.performed.symm.trans expected)
    have endpoint := facts.finalEndpoint
    rw [same] at endpoint
    have written := GeneralBorrowNormalStoredWriteback.stored tree location protections anchor facts.index .Read mode facts.newState facts.finalStored
    rw [index] at written
    simp only [written,Option.getD_some]
    exact endpoint.symm.trans (congrArg LocationState.permission old)
  · let schedule := normal.topology.traverse anchor.toNat mode (sourceNormalSkipped normal .Read)
    have completed := (GeneralBorrowProtectedReadInvariant.normal normal forest anchor.toNat
      (GeneralBorrowProtectedReadPermissionMetadata.valid_anchor tree location protections anchor anchorNode anchorPresent) mode
      (GeneralBorrowProtectedReadPermissionMetadata.projection_aligned tree location protections) initial).1
    have actual := GeneralBorrowStorage.events_visited schedule.2 schedule.1 .Read normal completed
    change (normal.performAccess anchor.toNat .Read mode).visited = schedule.2 at actual
    have outside : ∀ event ∈ schedule.2,event.node ≠ query.toNat := by
      intro event member same
      exact visited (List.mem_map.mpr ⟨event,by rw [actual];exact member,same⟩)
    have same := GeneralBorrowTwoRootNormalAccess.normal_unvisited tree location protections anchor query node .Read mode present outside
    rw [same]

/-- The all-exposed stable permission invariant survives actual normal Reads. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (mode : ChildrenVisitMode) (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (initial : GeneralBorrowProtectedReadInvariant.Data (source_normal_projection tree location protections))
    (stable : AllExposed tree location) :
    AllExposed tree (tree.performNormalAccessAt location anchor .Read protections mode).location := by
  intro query node present exposed
  rw [normal_permission tree location protections anchor mode depth children anchorNode anchorPresent forest initial query node present
    (stable query node present exposed)]
  exact stable query node present exposed

/-- Read-stable exposed permissions justify ANY actual/virtual held-mask
comparison. This is the pending-map bridge, independent of cache coherence. -/
theorem virtual (tree : BorrowTree) (location : LocationTree) (actual pending : ProtectedTags) (stable : AllExposed tree location) :
    GeneralBorrowProtectedVirtualReadCache.Stable tree location actual pending := by
  intro index node present exposed _
  exact ⟨(location.perms.get index).getD node.defaultLocationState,by simp [BorrowTree.locationStateAt,present],stable index node present exposed⟩

theorem location (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor root : UniIndex) (mode : ChildrenVisitMode) (range : ByteRange)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (initial : GeneralBorrowProtectedReadInvariant.Data (source_normal_projection tree location protections))
    (stable : AllExposed tree location) :
    AllExposed tree (source_access_location (source_tree_access_at tree location (some anchor) .Read protections mode range)) := by
  have valid := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor tree location protections anchor anchorNode anchorPresent
  have compatible := GeneralBorrowProtectedReadPermissionMetadata.compatible_initial tree location protections anchor initial
  rw [GeneralBorrowProtectedReadSingleRoot.single_root_location tree location protections anchor root mode range forest valid compatible
    depth children anchorNode anchorPresent roots covered]
  exact normal tree location protections anchor mode depth children anchorNode anchorPresent forest initial stable
end DuplicatePrefix.GeneralBorrowProtectedReadStable
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReadStable.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected Read stable dependency {dependency}"
