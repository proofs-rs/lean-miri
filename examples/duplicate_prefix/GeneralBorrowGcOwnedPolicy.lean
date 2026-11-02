import duplicate_prefix.GeneralBorrowGcLocalEffectivePolicy
import duplicate_prefix.GeneralBorrowRange

namespace DuplicatePrefix.GeneralBorrowGcOwnedPolicy
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowAnchor DuplicatePrefix.GeneralBorrowPermissions
open DuplicatePrefix.GeneralBorrowGcLocalEffectivePolicy DuplicatePrefix.GeneralRangeMapOrigins

/-- Record each effective permission against its pre-GC anchor relation.
Topology is independent of the location payload. -/
def Allowed (tree : BorrowTree) (anchor : UniIndex) (kind : AccessKind)
    (query : UniIndex) (state : LocationState) : Prop :=
  let location : LocationTree := ⟨⟨#[]⟩,{}⟩
  AccessOwned state kind (relation (source_normal_projection tree location {}) anchor.toNat query.toNat) false

/-- Range-local ownership establishes the surviving-node effective policy;
vacant Clean is kept separately, without assuming materialized permissions. -/
theorem of_owned (tree : BorrowTree) (anchor : UniIndex) (kind : AccessKind) (lower upper : UInt64)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree {} anchor kind) lower upper tree.locations)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree) :
    Policy (Allowed tree anchor kind) lower upper tree := by
  refine ⟨?_,clean⟩
  intro query node present position valid positive before after
  let location := tree.locations.entries[position].data
  have owner := (owned position valid positive before after).2
  have bound : query.toNat < (source_normal_projection tree location {}).topology.nodes.size := by
    have size : (source_normal_projection tree location {}).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
    rw [size]
    exact GeneralBorrowNodeUpdate.lookup_valid tree.nodes query node present
  obtain ⟨state,stored,permission⟩ := owner.permissions query.toNat bound
  have exactState := projection_state tree location {} query.toNat query node
    (index_self query) rfl present
  have equal : state = (location.perms.get query).getD node.defaultLocationState :=
    Option.some.inj (stored.symm.trans exactState)
  subst state
  have empty : (source_normal_projection tree location {}).protectedNodes = [] := by
    unfold_general_projection;simp [ProtectedTags.contains,ProtectedTags.get]
  have topology : (source_normal_projection tree location {}).topology =
      (source_normal_projection tree (⟨⟨#[]⟩,{}⟩ : LocationTree) {}).topology := rfl
  have relationEq : relation (source_normal_projection tree location {}) anchor.toNat query.toNat =
      relation (source_normal_projection tree (⟨⟨#[]⟩,{}⟩ : LocationTree) {}) anchor.toNat query.toNat :=
    congrArg (fun (topology : TraversalTree) => if query.toNat ∈ topology.ancestorPath anchor.toNat then
      AccessRelatedness.LocalAccess else AccessRelatedness.ForeignAccess) topology
  have held : (source_normal_projection tree location {}).protectedNodes.contains query.toNat = false := by rw [empty];rfl
  change AccessOwned ((location.perms.get query).getD node.defaultLocationState) kind
    (relation (source_normal_projection tree location {}) anchor.toNat query.toNat)
    ((source_normal_projection tree location {}).protectedNodes.contains query.toNat) at permission
  rw [relationEq,held] at permission
  exact permission

/-- Actual arbitrary-tree fullGC preserves the range-local effective permission
constraints obtained from the incoming owner's pre-GC ancestor relation. This
is a permission frame; retained-node topology and GC success are separate. -/
theorem collect (tree : BorrowTree) (anchor : UniIndex) (kind : AccessKind) (lower upper : UInt64)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree {} anchor kind) lower upper tree.locations)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree) (live : Array BorTag) :
    Policy (Allowed tree anchor kind) lower upper (tree.removeUnreachableTags live).tree :=
  GeneralBorrowGcLocalEffectivePolicy.preserves _ lower upper tree live (of_owned tree anchor kind lower upper owned clean)
end DuplicatePrefix.GeneralBorrowGcOwnedPolicy
