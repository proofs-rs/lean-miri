import duplicate_prefix.GeneralBorrowSharedGeneratorProfile
import duplicate_prefix.GeneralBorrowGeneratedStarShape
import duplicate_prefix.GeneralBorrowFrozenWriteEvents

namespace DuplicatePrefix.GeneralBorrowFrozenStarSchedule
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowTopology DuplicatePrefix.GeneralBorrowFrontier DuplicatePrefix.GeneralBorrowPresence
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowGeneratedStarShape
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The real root's ancestor path is a singleton, independently of sparse slots. -/
theorem root_path (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (node : TreeNode)
    (present : tree.nodeAt root = some node) (parentless : node.parent = none) :
    (source_normal_projection tree location {}).topology.ancestorPath root.toNat = [root.toNat] := by
  have parent : (nodeData (source_normal_projection tree location {}).topology root.toNat).parent = none := by
    dsimp only [nodeData]
    rw [projection_topology_node tree location {} root.toNat root node rfl present]
    simp only [parentless,Option.map_none]
  change sourceAncestorPath (source_normal_projection tree location {}).topology
    (source_normal_projection tree location {}).topology.nodes.size root.toNat = _
  cases (source_normal_projection tree location {}).topology.nodes.size with
  | zero => rfl
  | succ fuel => rw [ancestor_succ,parent]

/-- The generated exact Frozen/Read-SIFA leaf is not pruned by a foreign Write.
The SIFA condition is derived from the profile, not merely its permission. -/
theorem leaf_unskipped (tree : BorrowTree) (location : LocationTree) (root leaf : UniIndex) (node : TreeNode)
    (present : tree.nodeAt leaf = some node) (different : leaf ≠ root)
    (profile : GeneralBorrowSharedGeneratorProfile.Profile tree location root) :
    leaf.toNat ∉ sourceNormalSkipped (source_normal_projection tree location {}) .Write := by
  have state : (source_normal_projection tree location {}).stateAt leaf.toNat = some GeneralBorrowFreshAnchor.sharedState := by
    rw [projection_state tree location {} leaf.toNat leaf node (index_self leaf) rfl present,profile.shared leaf node present different]
    rfl
  have valid : leaf.toNat < (source_normal_projection tree location {}).topology.nodes.size := by
    have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes leaf node present
    unfold_general_projection;unfold_general_topology
    simpa only [Array.size_map] using valid
  rw [skipped_iff _ .Write leaf.toNat _ state valid]
  decide

private theorem flatMap_single {α β : Type} (items : List α) (f : α → List β) (g : α → β)
    (single : ∀ x ∈ items, f x = [g x]) : items.flatMap f = items.map g := by
  induction items with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.flatMap_cons,List.map_cons,single head (by simp),List.singleton_append]
    rw [ih (fun x member => single x (by simp [member]))]

/-- Exact source normal root-Write schedule: root Local first, then every
actual child exactly once in source reverse order as a Foreign visitor. -/
theorem schedule (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (node : TreeNode)
    (star : Star tree root node) (profile : GeneralBorrowSharedGeneratorProfile.Profile tree location root) :
    ((source_normal_projection tree location {}).topology.traverse root.toNat .VisitChildrenOfAccessed
      (sourceNormalSkipped (source_normal_projection tree location {}) .Write)).2 =
      ⟨root.toNat,.LocalAccess⟩ :: node.children.toList.reverse.map (fun index => ⟨index.toNat,.ForeignAccess⟩) := by
  let normal := source_normal_projection tree location {}
  have path := root_path tree location root node star.present star.parentless
  have roots : sourceForeignRoots normal.topology [root.toNat] .VisitChildrenOfAccessed = node.children.toList.reverse.map UniIndex.toNat := by
    change sourceForeignRootsGo normal.topology .VisitChildrenOfAccessed [root.toNat] none true = _
    rw [roots_cons,roots_nil]
    simp only [deferredHeads,Bool.not_true,Bool.false_or,beq_self_eq_true,ite_true,List.append_nil]
    change ((nodeData normal.topology root.toNat).children.reverse.filter (fun child => (none : Option Nat) != some child)) = _
    dsimp only [normal,nodeData]
    rw [projection_topology_node tree location {} root.toNat root node rfl star.present]
    simp [List.map_reverse]
  have leafEvent : ∀ index ∈ node.children.toList.reverse,
      sourceForeignPostorder normal.topology (sourceNormalSkipped normal .Write) normal.topology.nodes.size index.toNat = [⟨index.toNat,.ForeignAccess⟩] := by
    intro index member
    have listed := (star.children index).mp (List.mem_reverse.mp member)
    obtain ⟨child,childPresent⟩ := listed.2
    have leaf := (star.leaves index child childPresent listed.1).2
    have shape : (nodeData normal.topology index.toNat).children = [] := by
      dsimp only [normal,nodeData]
      rw [projection_topology_node tree location {} index.toNat index child rfl childPresent]
      simp only [leaf,Array.toList_empty,List.map_nil]
    have active := leaf_unskipped tree location root index child childPresent listed.1 profile
    have contains : (sourceNormalSkipped normal .Write).contains index.toNat = false := by
      cases known : (sourceNormalSkipped normal .Write).contains index.toNat with
      | false => rfl
      | true => exact False.elim (active (List.contains_iff_mem.mp known))
    have nonempty : 0 < normal.topology.nodes.size := by
      have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root node star.present
      have size : normal.topology.nodes.size = tree.nodes.data.size := by dsimp only [normal];unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
      omega
    cases sizeEq : normal.topology.nodes.size with
    | zero => omega
    | succ fuel => rw [foreign_succ,contains];simp only [Bool.false_eq_true,ite_false,shape,List.reverse_nil,List.flatMap_nil,List.nil_append]
  change ((normal.topology.ancestorPath root.toNat).map (fun index => ⟨index,.LocalAccess⟩) ++
    (sourceForeignRoots normal.topology (normal.topology.ancestorPath root.toNat) .VisitChildrenOfAccessed).flatMap
      (sourceForeignPostorder normal.topology (sourceNormalSkipped normal .Write) normal.topology.nodes.size)) = _
  rw [path,roots]
  simp only [List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.flatMap_map]
  rw [flatMap_single _ _ _ leafEvent]

end DuplicatePrefix.GeneralBorrowFrozenStarSchedule
