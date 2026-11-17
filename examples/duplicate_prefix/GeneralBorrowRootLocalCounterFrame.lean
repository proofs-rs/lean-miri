import duplicate_prefix.GeneralBorrowSnapshotAnyKindTransport
namespace DuplicatePrefix.GeneralBorrowRootLocalCounterFrame
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowProjection GeneralBorrowForest
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Coherent counters below one physical root depend only on permissions in
that root's actual ancestor-walk component. This needs no global counter frame
and applies to Read and Write with any tag cutoff. Operational callers derive
the slot frame from the real operation and graph separation. -/
theorem counter_frame (tree : BorrowTree) (before after : LocationTree)
    (protections : ProtectedTags) (root query : UniIndex) (kind : AccessKind)
    (oldCoherent : LocationCoherent tree before protections)
    (newCoherent : LocationCoherent tree after protections)
    (covers : Covers tree.nodes root query)
    (slots : ∀ index node, tree.nodes.get index = some node →
      root ∈ walk tree.nodes (tree.nodes.size+1) index → after.perms.get index = before.perms.get index) :
    counter after.exposedCache query kind = counter before.exposedCache query kind := by
  rw [newCoherent query kind,oldCoherent query kind]
  congr 1
  unfold cardinality
  congr 1
  apply List.filter_congr
  intro row member
  by_cases path : query ∈ walk tree.nodes (tree.nodes.size+1) row.1
  · have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
    have same := slots row.1 row.2 present (covers row member path)
    simp only [contributes,GeneralBorrowExposureCardinality.effective,same]
  · have absent : (walk tree.nodes (tree.nodes.size+1) row.1).contains query = false := by
      apply Bool.eq_false_iff.mpr
      intro positive
      exact path (List.contains_iff_mem.mp positive)
    simp only [contributes,absent,Bool.and_false]

/-- Root-local counter equality suffices to transport any-kind snapshots;
unrelated roots may change both kinds of counter. -/
theorem snapshot (tree : BorrowTree) (before after : LocationTree)
    (protections : ProtectedTags) (root : UniIndex) (position : Nat)
    (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (old : Snapshot tree before protections root position maximum kind support)
    (oldCoherent : LocationCoherent tree before protections)
    (newCoherent : LocationCoherent tree after protections)
    (covers : ∀ index, support index → Covers tree.nodes root index)
    (componentSlots : ∀ index node, tree.nodes.get index = some node →
      root ∈ walk tree.nodes (tree.nodes.size+1) index → after.perms.get index = before.perms.get index)
    (supportSlots : ∀ index, support index → after.perms.get index = before.perms.get index) :
    Snapshot tree after protections root position maximum kind support := by
  have rootFrame := counter_frame tree before after protections root root kind oldCoherent newCoherent (fun _ _ h => h) componentSlots
  refine ⟨?_,?_⟩
  · intro index node included present
    have indexFrame := counter_frame tree before after protections root index kind oldCoherent newCoherent (covers index included) componentSlots
    have classifyFrame : relation after root index node maximum kind position = relation before root index node maximum kind position := by
      have rootCount := congrArg UInt16.toNat rootFrame
      have indexCount := congrArg UInt16.toNat indexFrame
      cases kind <;> simp only [GeneralBorrowExposureCardinality.counter] at rootCount indexCount <;> simp only [relation,GeneralBorrowWildcardRelatednessBounds.count,rootCount,indexCount]
    rw [classifyFrame]
    change Scalar (GeneralBorrowWildcardVirtualLeaf.effective after index node) kind _ _
    simpa only [GeneralBorrowWildcardVirtualLeaf.effective,supportSlots index included] using old.scalar index node included present
  · intro physical
    obtain ⟨index,node,included,present,witness⟩ := old.witness physical
    exact ⟨index,node,included,present,by simpa only [Supports,supportSlots index included] using witness⟩

/-- Actual ancestor-walk components of distinct physical roots are disjoint. -/
theorem components_disjoint (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (left right index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (leftMember : left ∈ tree.roots.toList) (rightMember : right ∈ tree.roots.toList)
    (different : left ≠ right)
    (leftWalk : left ∈ walk tree.nodes (tree.nodes.size+1) index)
    (rightWalk : right ∈ walk tree.nodes (tree.nodes.size+1) index) : False := by
  obtain ⟨depth⟩ := formed.depth
  let topology := (source_normal_projection tree location protections).topology
  have leftPath := GeneralBorrowPhysicalRootPath.projection_desc tree location protections left index
    (GeneralBorrowWildcardControlWitness.path_of_walk tree depth left index node present _ leftWalk)
  have rightPath := GeneralBorrowPhysicalRootPath.projection_desc tree location protections right index
    (GeneralBorrowWildcardControlWitness.path_of_walk tree depth right index node present _ rightWalk)
  have parentless : ∀ root, root ∈ tree.roots.toList →
      ∃ valid : root.toNat < topology.nodes.size, topology.nodes[root.toNat].parent = none := by
    intro root member
    obtain ⟨rootNode, rootPresent, rootParentless⟩ := formed.rootNodes root member
    have valid : root.toNat < topology.nodes.size := by
      have bound := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root rootNode rootPresent
      unfold topology
      unfold_general_projection
      unfold_general_topology
      simpa only [Array.size_map] using bound
    refine ⟨valid, ?_⟩
    have projected := projection_topology_node tree location protections root.toNat root rootNode rfl rootPresent
    change (topology.nodes[root.toNat]?.getD ⟨none, []⟩) = _ at projected
    simp only [Array.getElem?_eq_getElem valid, Option.getD_some] at projected
    rw [projected]
    simp only [rootParentless, Option.map_none]
  obtain ⟨leftValid, leftParentless⟩ := parentless left leftMember
  obtain ⟨rightValid, rightParentless⟩ := parentless right rightMember
  apply GeneralBorrowNormalComponentNormalization.roots_disjoint topology left.toNat right.toNat index.toNat
    leftValid rightValid leftParentless rightParentless _ leftPath rightPath
  intro same
  exact different (GeneralBorrowNodeUpdate.index_injective left right same)

/-- Any-kind, any-cutoff Snapshot of another physical root survives an actual
outside-slot frame and coherent caches. Both kinds of global counters may
change in the operated component. No separation premise is supplied. -/
theorem snapshot_other (tree : BorrowTree) (before after : LocationTree)
    (protections : ProtectedTags) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root other : UniIndex) (rootMember : root ∈ tree.roots.toList)
    (otherMember : other ∈ tree.roots.toList) (different : root ≠ other)
    (support otherSupport : UniIndex → Prop)
    (covers : ∀ index, support index → Covers tree.nodes root index)
    (otherCovers : ∀ index, otherSupport index → Covers tree.nodes other index)
    (otherPresent : ∀ index, otherSupport index → ∃ node, tree.nodes.get index = some node)
    (position : Nat) (maximum : Option BorTag) (kind : AccessKind)
    (old : Snapshot tree before protections other position maximum kind otherSupport)
    (oldCoherent : LocationCoherent tree before protections)
    (newCoherent : LocationCoherent tree after protections)
    (outside : ∀ index, ¬support index → after.perms.get index = before.perms.get index) :
    Snapshot tree after protections other position maximum kind otherSupport := by
  have componentSlots : ∀ index node, tree.nodes.get index = some node →
      other ∈ walk tree.nodes (tree.nodes.size+1) index → after.perms.get index = before.perms.get index := by
    intro index node present inOther
    apply outside index
    intro inside
    have own : index ∈ walk tree.nodes (tree.nodes.size+1) index := by simp [walk]
    have inRoot := covers index inside (index,node) ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present) own
    exact components_disjoint tree before protections formed root other index node present rootMember otherMember different inRoot inOther
  apply snapshot tree before after protections other position maximum kind otherSupport old oldCoherent newCoherent otherCovers componentSlots
  intro index included
  obtain ⟨node,present⟩ := otherPresent index included
  apply componentSlots index node present
  apply otherCovers index included (index,node) ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)
  simp [walk]


/-- Full no-cutoff authorization of another root follows from the same local
frames. Empty residual masks are derived from their actual definition. -/
theorem authorization_other_no_maximum (tree : BorrowTree) (before after : LocationTree)
    (protections : ProtectedTags) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root other : UniIndex) (rootMember : root ∈ tree.roots.toList)
    (otherMember : other ∈ tree.roots.toList) (different : root ≠ other)
    (support otherSupport : UniIndex → Prop)
    (covers : ∀ index, support index → Covers tree.nodes root index)
    (position : Nat) (kind : AccessKind)
    (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree before protections other position none kind otherSupport)
    (oldCoherent : LocationCoherent tree before protections)
    (newCoherent : LocationCoherent tree after protections) (short : tree.nodes.size < 65536)
    (outside : ∀ index, ¬support index → after.perms.get index = before.perms.get index) :
    DuplicatePrefixResidualSupportAuthorization.Authorization tree after protections other position none kind otherSupport := by
  have initial := DuplicatePrefixResidualInitialSnapshot.snapshot tree before protections other position none kind otherSupport authorization oldCoherent short
  have current := snapshot_other tree before after protections formed root other rootMember otherMember different support otherSupport covers authorization.covers authorization.present position none kind initial oldCoherent newCoherent outside
  exact DuplicatePrefixResidualSupportSnapshotBridge.of_snapshot tree after protections other position none kind otherSupport current authorization.rooted authorization.present authorization.children authorization.covers newCoherent short
    (fun removed legal => DuplicatePrefixResidualSupportAuthorization.no_maximum_removal_empty tree after protections kind removed legal)
end DuplicatePrefix.GeneralBorrowRootLocalCounterFrame
