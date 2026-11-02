import duplicate_prefix.GeneralBorrowFreshReleaseMixed
import duplicate_prefix.GeneralBorrowFreshWriteRestore
namespace DuplicatePrefix.GeneralBorrowFreshLifetimeRestore
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

set_option autoImplicit false in
/-- Metadata-only conditions for returning from a shared local path to an
older mutable anchor. Multiple read-only nodes may leave the local path, but
every such node must be unprotected in the actual post-endCall tag table. -/
structure RestoreTo (tree : BorrowTree) (before after : ProtectedTags)
    (child target : UniIndex) (writable : Nat → Bool) : Prop where
  targetValid : target.toNat < tree.nodes.data.size
  localRetained : ∀ (location : LocationTree) position,
    GeneralBorrowAnchor.relation (source_normal_projection tree location before) target.toNat position = .LocalAccess →
      GeneralBorrowAnchor.relation (source_normal_projection tree location before) child.toNat position = .LocalAccess ∧ writable position = true
  leavingReleased : ∀ (location : LocationTree) position,
    GeneralBorrowAnchor.relation (source_normal_projection tree location before) child.toNat position = .LocalAccess →
    GeneralBorrowAnchor.relation (source_normal_projection tree location before) target.toNat position = .ForeignAccess →
      (source_normal_projection tree location after).protectedNodes.contains position = false

theorem restore_map (tree : BorrowTree) (locations : Miri.DataStructures.DedupRangeMap LocationTree)
    (before after : ProtectedTags) (child target : UniIndex) (writable : Nat → Bool)
    (data : RestoreTo tree before after child target writable) :
    RestoreTo {tree with locations := locations} before after child target writable :=
  ⟨data.targetValid,data.localRetained,data.leavingReleased⟩

private theorem topology_size (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map]

/-- Recover actual Write ownership of any older anchor from mixed data after
real protector-table weakening. Child Read ownership alone is insufficient;
the retained local nodes must carry the explicit mixed Write strength. -/
theorem restore_location (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (weaken : ∀ tag, after.contains tag = true → before.contains tag = true)
    (child target : UniIndex) (writable : Nat → Bool) (data : RestoreTo tree before after child target writable)
    (owned : Combined tree before child writable location) :
    GeneralBorrowRange.LocationOwned tree after target .Write location := by
  obtain ⟨⟨forest,owner⟩,mixed⟩ := owned
  unfold GeneralBorrowRange.LocationOwned
  rw [GeneralBorrowFreshProtectorRelease.projection_protections tree location before after]
  refine ⟨forest,?_⟩
  apply GeneralBorrowFreshWriteRestore.mixed_owned _ target.toNat
    (by rw [topology_size];exact data.targetValid) owner.locationsAligned owner.defaultsAligned
    writable (GeneralBorrowAnchor.relation (source_normal_projection tree location before) child.toNat) mixed
  · exact GeneralBorrowFreshProtectorRelease.projection_weakens tree location before after weaken
  · exact data.localRetained location
  · exact data.leavingReleased location

theorem restore_owned_on (tree : BorrowTree) (before after : ProtectedTags)
    (weaken : ∀ tag, after.contains tag = true → before.contains tag = true)
    (child target : UniIndex) (writable : Nat → Bool) (data : RestoreTo tree before after child target writable)
    (lower upper : UInt64) (owned : OwnedOn (Combined tree before child writable) lower upper tree.locations) :
    OwnedOn (GeneralBorrowRange.LocationOwned tree after target .Write) lower upper tree.locations := by
  intro position valid positive start stop
  exact restore_location tree _ before after weaken child target writable data (owned position valid positive start stop)
end DuplicatePrefix.GeneralBorrowFreshLifetimeRestore
#print axioms DuplicatePrefix.GeneralBorrowFreshLifetimeRestore.restore_owned_on
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshLifetimeRestore." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved old mutable anchor restoration dependency {dependency}"
