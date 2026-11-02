import duplicate_prefix.GeneralBorrowExposedScopedOwnership
import duplicate_prefix.GeneralBorrowFreshLifetimeRestore
namespace DuplicatePrefix.GeneralBorrowExposedScopedRestore
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowAnchor DuplicatePrefix.GeneralBorrowPermissions
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
private theorem required_possible (state : LocationState) (writable : Bool)
    (related : AccessRelatedness) (held : Bool) (owned : Required state writable related held) :
    state.possible = true := by
  cases writable <;> cases related <;> exact owned.1

/-- Restore an arbitrary mutable anchor from a mixed invariant. Multiple Frozen
ancestors may remain read-only: those leaving the local path must be unprotected.
Every node retained on the target local path must carry actual Write strength. -/
theorem mixed_owned (support : Nat → Prop) (tree : NormalTreeState) (anchor : Nat)
    (valid : anchor < tree.topology.nodes.size)
    (locations : tree.locationStates.size = tree.topology.nodes.size)
    (defaults : tree.defaultStates.size = tree.topology.nodes.size)
    (writable : Nat → Bool) (beforeRelation : Nat → AccessRelatedness)
    (mixed : GeneralBorrowExposedScopedOwnership.Pointwise support tree writable beforeRelation)
    (protections : List Nat)
    (weaken : ∀ position, protections.contains position = true → tree.protectedNodes.contains position = true)
    (localRetained : ∀ position, relation tree anchor position = .LocalAccess →
      beforeRelation position = .LocalAccess ∧ writable position = true)
    (leavingReleased : ∀ position, beforeRelation position = .LocalAccess →
      relation tree anchor position = .ForeignAccess → protections.contains position = false) :
    GeneralBorrowExposedScopedOwnership.Pointwise support {tree with protectedNodes := protections}
      (fun _ => true) (relation tree anchor) := by
  intro position supported bound
  obtain ⟨state,present,permission⟩ := mixed position supported bound
  refine ⟨state,present,?_⟩
  change AccessOwned state .Write (relation tree anchor position) (protections.contains position)
  cases target : relation tree anchor position with
  | LocalAccess =>
    obtain ⟨beforeLocal,written⟩ := localRetained position target
    apply owned_release state .LocalAccess (tree.protectedNodes.contains position)
      (protections.contains position) (weaken position)
    simpa only [Required,written,↓reduceIte,beforeLocal] using permission
  | ForeignAccess =>
    cases earlier : beforeRelation position with
    | LocalAccess =>
      rw [leavingReleased position earlier target]
      exact ⟨required_possible state (writable position) (beforeRelation position)
        (tree.protectedNodes.contains position) permission,Or.inl rfl⟩
    | ForeignAccess =>
      apply owned_release state .ForeignAccess (tree.protectedNodes.contains position)
        (protections.contains position) (weaken position)
      cases label : writable position <;>
        simpa [Required,label,earlier,AccessOwned] using permission

/-- Actual post-endCall table weakening restores the selected older Write
anchor without imposing ownership on exposed components outside its support. -/
theorem location (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (weaken : ∀ tag, after.contains tag = true → before.contains tag = true)
    (child target : UniIndex) (support : Nat → Prop) (writable : Nat → Bool)
    (data : GeneralBorrowFreshLifetimeRestore.RestoreTo tree before after child target writable)
    (mixed : GeneralBorrowExposedScopedOwnership.Pointwise support (source_normal_projection tree location before)
      writable (relation (source_normal_projection tree location before) child.toNat)) :
    GeneralBorrowExposedScopedOwnership.Pointwise support (source_normal_projection tree location after)
      (fun _ => true) (relation (source_normal_projection tree location after) target.toNat) := by
  rw [GeneralBorrowFreshProtectorRelease.projection_protections tree location before after]
  apply mixed_owned support (source_normal_projection tree location before) target.toNat
    (by unfold_general_projection;unfold_general_topology;simp only [Array.size_map];exact data.targetValid)
    (by unfold_general_projection;unfold_general_topology;simp only [Array.size_mapIdx,Array.size_map])
    (by unfold_general_projection;unfold_general_topology;simp only [Array.size_map])
    writable (relation (source_normal_projection tree location before) child.toNat) mixed
  · exact GeneralBorrowFreshProtectorRelease.projection_weakens tree location before after weaken
  · exact data.localRetained location
  · exact data.leavingReleased location

end DuplicatePrefix.GeneralBorrowExposedScopedRestore
