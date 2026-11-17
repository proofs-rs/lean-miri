import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadData
import duplicate_prefix.GeneralBorrowSparseExposedLeafState
import duplicate_prefix.GeneralBorrowExposedScopedInactiveLeafSeed
import duplicate_prefix.GeneralBorrowProtectorCacheMap
import duplicate_prefix.GeneralBorrowFreshProtectorRelease
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableReadWeaken
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Real table weakening retains the full mixed Read input when every exposed
node's protector membership is unchanged. Hidden released tags are unrestricted. -/
noncomputable def weaken (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (weaker : ∀ tag,after.contains tag=true → before.contains tag=true)
    (exposedSame : ∀ index node,tree.nodeAt index=some node → node.isExposed=true → after.contains node.tag=before.contains node.tag)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop) (writable : Nat → Bool)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (data : GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location before anchor selected head tail support writable) :
    GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location after anchor selected head tail support writable := by
  let base := data.base.base
  have mixed : GeneralBorrowExposedScopedInactiveMixedRangeData.Mixed tree location after anchor support writable := by
    unfold GeneralBorrowExposedScopedInactiveMixedRangeData.Mixed
    rw [GeneralBorrowFreshProtectorRelease.projection_protections tree location before after]
    intro position included valid
    obtain ⟨state,present,allowed⟩ := data.base.mixed position included valid
    exact ⟨state,present,GeneralBorrowRelease.required_weakens state (writable position) _ _ _
      (GeneralBorrowFreshProtectorRelease.projection_weakens tree location before after weaker position) allowed⟩
  have coherent := GeneralBorrowProtectorCacheMap.frame tree location before after base.coherent exposedSame
  have writableLeaves : ∀ index node,area.support index→tree.nodeAt index=some node→
      GeneralBorrowExposedConditionalWritePermissions.Compatible (GeneralBorrowWildcardVirtualLeaf.effective location index node)
        .LocalAccess (after.contains node.tag) := by
    intro index node included present
    obtain ⟨actual,lookup,leaf,exposed⟩:=data.leaves index included
    have equal : actual=node:=Option.some.inj (lookup.symm.trans present)
    subst actual
    rw [exposedSame index node present exposed]
    exact data.writableLeaves index node included present
  let restored : GeneralBorrowExposedScopedInactiveRangeData.Data tree location after anchor selected head tail support := by
    apply GeneralBorrowExposedScopedInactiveLeafSeed.seed tree location after anchor selected head tail support writable context
      base.forest base.component data.base.support_eq mixed base.rootPath base.ancestors base.separate coherent data.short
    · intro query included
      obtain ⟨node,present,leaf,exposed⟩ := data.leaves query included
      refine ⟨node,present,leaf,exposed,?_,?_⟩
      · exact GeneralBorrowSparseExposedLeafState.supports _ _ (writableLeaves query node included present) .Read
      · exact (writableLeaves query node included present).1
    · intro different
      exact (base.primary different).base.included head (base.primary different).base.rooted
    · intro root member different
      exact (base.virtual root member different).included root (base.virtual root member different).rooted
  exact ⟨⟨restored,data.base.support_eq,mixed⟩,data.short,data.leaves,writableLeaves⟩
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableReadWeaken
