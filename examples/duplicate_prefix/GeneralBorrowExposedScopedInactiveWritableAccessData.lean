import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadRange
import duplicate_prefix.GeneralBorrowExposedScopedOwnership
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableAccessData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
variable [area : GeneralBorrowExposedKnownRootState.Scope]
/-- One persistent BOTH-kind contract. The exposed selected component keeps
its exact Unique/Disabled profile; hidden or Unique-only substitutes are absent. -/
abbrev Data (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat→Prop) :=
  GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location protections anchor selected head tail support (fun _=>true)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def owned {tree location protections anchor selected head tail support}
    (data : Data tree location protections anchor selected head tail support) (kind : AccessKind) :
    GeneralBorrowExposedScopedNormal.Owned (source_normal_projection tree location protections) anchor.toNat kind data.base.base.component := by
  cases kind with
  | Read=>exact data.base.base.owned
  | Write=>
    intro index included valid
    have size : (source_normal_projection tree location protections).locationStates.size=(source_normal_projection tree location protections).topology.nodes.size := by
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_mapIdx,Array.size_map]
    obtain ⟨state,present,permission⟩:=data.base.mixed index (by rw [←data.base.support_eq];exact included) (by rw [size];exact valid)
    exact ⟨state,present,(by simpa only [GeneralBorrowPermissions.Required,GeneralBorrowPermissions.AccessOwned,Bool.true_eq,ite_true] using permission)⟩
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableAccessData
