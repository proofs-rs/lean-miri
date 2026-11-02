import duplicate_prefix.GeneralBorrowFreshReadFrame
import duplicate_prefix.GeneralBorrowRelease
namespace DuplicatePrefix.GeneralBorrowFreshProtectorRelease
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- A weaker tag table produces a weaker real normal-projection protector
list, including sparse/missing node tables. No lookup-success assumption is used. -/
theorem projection_weakens (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (weaken : ∀ tag, after.contains tag = true → before.contains tag = true) (position : Nat)
    (held : (source_normal_projection tree location after).protectedNodes.contains position = true) :
    (source_normal_projection tree location before).protectedNodes.contains position = true := by
  revert held
  unfold_general_projection
  simp only [List.contains_iff_mem,List.mem_filterMap]
  intro held
  obtain ⟨⟨index,node⟩,member,selected⟩ := held
  have choice : index.toNat = position ∧ after.contains node.tag = true := by
    split at selected
    next active => exact ⟨Option.some.inj selected,active⟩
    next => contradiction
  exact ⟨(index,node),member,by simp only [weaken node.tag choice.2,↓reduceIte,choice.1]⟩

theorem projection_protections (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags) :
    source_normal_projection tree location after =
      {source_normal_projection tree location before with
        protectedNodes := (source_normal_projection tree location after).protectedNodes} := rfl

private theorem access_weakens (state : LocationState) (kind : AccessKind) (related : AccessRelatedness)
    (before after : Bool) (weaken : after = true → before = true)
    (owned : GeneralBorrowPermissions.AccessOwned state kind related before) :
    GeneralBorrowPermissions.AccessOwned state kind related after := by
  cases kind <;> cases related
  · exact owned
  · exact GeneralBorrowPermissions.owned_release state .ForeignAccess before after weaken owned
  · exact GeneralBorrowPermissions.owned_release state .LocalAccess before after weaken owned
  · exact GeneralBorrowPermissions.owned_release state .ForeignAccess before after weaken owned

theorem anchor_weakens (tree : NormalTreeState) (protections : List Nat)
    (weaken : ∀ position, protections.contains position = true → tree.protectedNodes.contains position = true)
    (anchor : Nat) (kind : AccessKind) (owned : GeneralBorrowAnchor.AnchorOwned tree anchor kind) :
    GeneralBorrowAnchor.AnchorOwned {tree with protectedNodes := protections} anchor kind := by
  refine ⟨owned.anchorValid,owned.locationsAligned,owned.defaultsAligned,?_⟩
  intro position valid
  obtain ⟨state,present,permitted⟩ := owned.permissions position valid
  exact ⟨state,present,access_weakens state kind _ _ _ (weaken position) permitted⟩

/-- Real tag removal preserves an existing anchor's ownership. It changes
neither its permission data nor its topology. -/
theorem location_weakens (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (weaken : ∀ tag, after.contains tag = true → before.contains tag = true)
    (anchor : UniIndex) (kind : AccessKind)
    (owned : GeneralBorrowRange.LocationOwned tree before anchor kind location) :
    GeneralBorrowRange.LocationOwned tree after anchor kind location := by
  obtain ⟨forest,owner⟩ := owned
  unfold GeneralBorrowRange.LocationOwned
  rw [projection_protections tree location before after]
  exact ⟨forest,anchor_weakens _ _ (projection_weakens tree location before after weaken) anchor.toNat kind owner⟩

theorem owned_on_weakens (tree : BorrowTree) (before after : ProtectedTags)
    (weaken : ∀ tag, after.contains tag = true → before.contains tag = true)
    (anchor : UniIndex) (kind : AccessKind) (lower upper : UInt64)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree before anchor kind) lower upper tree.locations) :
    OwnedOn (GeneralBorrowRange.LocationOwned tree after anchor kind) lower upper tree.locations := by
  intro position valid positive start stop
  exact location_weakens tree _ before after weaken anchor kind (owned position valid positive start stop)

/-- The actual global endCall fold preserves any existing slice ownership,
for an arbitrary frame protector list and arbitrary allocation history. -/
theorem end_call_owned_on (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (anchor : UniIndex) (kind : AccessKind) (lower upper : UInt64)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree global.protectedTags anchor kind) lower upper tree.locations) :
    OwnedOn (GeneralBorrowRange.LocationOwned tree (global.endCall frame).protectedTags anchor kind)
      lower upper tree.locations :=
  owned_on_weakens tree global.protectedTags (global.endCall frame).protectedTags
    (GeneralBorrowRelease.end_call_weakens global frame) anchor kind lower upper owned
end DuplicatePrefix.GeneralBorrowFreshProtectorRelease
#print axioms DuplicatePrefix.GeneralBorrowFreshProtectorRelease.end_call_owned_on
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshProtectorRelease." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved global protector removal dependency {dependency}"
