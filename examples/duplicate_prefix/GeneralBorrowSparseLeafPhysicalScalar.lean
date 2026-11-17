import duplicate_prefix.GeneralBorrowSparseExposedLeafAccess
import duplicate_prefix.GeneralBorrowWildcardSubtreeState
namespace DuplicatePrefix.GeneralBorrowSparseLeafPhysical
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf GeneralBorrowWildcardSubtreeState GeneralBorrowSparseExposedLeafState
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

theorem level_write (state : LocationState) (held : Bool)
    (good : GeneralBorrowExposedConditionalWritePermissions.Compatible state .LocalAccess held) :
    state.permission.strongestAllowedLocalAccess held=.Write := by
  have allows:=GeneralBorrowExposedConditionalWritePermissions.local_allows state held good
  cases eq : state.permission.strongestAllowedLocalAccess held <;> simp_all [WildcardAccessLevel.allows]

theorem local_transition (state : LocationState) (held : Bool)
    (good : GeneralBorrowExposedConditionalWritePermissions.Compatible state .LocalAccess held) (kind : AccessKind) :
    ∃next delta,state.performAccess kind .LocalAccess held=.Success next delta ∧
      GeneralBorrowExposedConditionalWritePermissions.Compatible next .LocalAccess held := by
  cases kind with
  | Write=> obtain ⟨next,delta,actual,compatible,_,_⟩:=GeneralBorrowExposedConditionalWritePermissions.transition state .LocalAccess held good;exact ⟨next,delta,actual,compatible⟩
  | Read=>
    have readable : GeneralBorrowProtectedReadCompatible.Compatible state .LocalAccess held:=⟨good.1,good.2.1⟩
    obtain ⟨next,delta,actual,compatible,support⟩:=GeneralBorrowExposedConditionalReadPermissions.transition state .LocalAccess held readable
    obtain ⟨same,change,actualSame,permission⟩:=GeneralBorrowExposedConditionalAccessSupport.local_read_levels state held readable
    have equal:=LocationState.AccessResult.Success.inj (actual.symm.trans actualSame)
    have nextPermission : next.permission=state.permission:=(congrArg LocationState.permission equal.1).trans permission
    exact ⟨next,delta,actual,compatible.1,by rw [nextPermission];exact good.2⟩

end
end DuplicatePrefix.GeneralBorrowSparseLeafPhysical
