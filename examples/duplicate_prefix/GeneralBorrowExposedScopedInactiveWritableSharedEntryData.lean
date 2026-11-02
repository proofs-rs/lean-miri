import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedProtect
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedData
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedEntryData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Tag allocator freshness and the actual graph-tag lookup invariant discharge
Strong registration and form the complete initial protected parent Read data. -/
theorem registered {profileMode : ProfileMode} (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor input protections selected head tail writable profileMode)
    (nodeTags : ∀ index node,input.tree.nodeAt index = some node → input.tree.indexOfTag node.tag = some index) :
    ∃ context : GeneralBorrowExposedKnownRootRangeData.Context input.tree input.parent selected head tail,
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data input.tree location
          (protections.insert input.newTag .StrongProtector) input.parent selected head tail raw.component.support writable))
        input.offset (input.offset+input.len) input.tree.locations := by
  have absent : input.tree.indexOfTag input.newTag = none := by
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find input.tree.tagMapping input.newTag input.fresh,Option.map_none]
  obtain ⟨held,support⟩ := GeneralBorrowExposedScopedInactiveWritableSharedProtect.protect input protections input.newTag selected head tail writable raw (by
    intro index node present equal
    have mapped := nodeTags index node present
    rw [equal,absent] at mapped
    cases mapped)
  obtain ⟨context,owned⟩ := GeneralBorrowExposedScopedInactiveWritableSharedData.build input
    (protections.insert input.newTag .StrongProtector) selected head tail writable held
  exact ⟨context,by simpa only [support] using owned⟩
/-- Existing physical validators need only the mixed base of the richer
writable rows; projection preserves the initial-state-only registration proof. -/
theorem registered_mixed {profileMode : ProfileMode} (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor input protections selected head tail writable profileMode)
    (nodeTags : ∀ index node,input.tree.nodeAt index=some node → input.tree.indexOfTag node.tag=some index) :
    ∃ context : GeneralBorrowExposedKnownRootRangeData.Context input.tree input.parent selected head tail,
      GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedInactiveMixedRangeData.Data input.tree location
        (protections.insert input.newTag .StrongProtector) input.parent selected head tail raw.component.support writable))
        input.offset (input.offset+input.len) input.tree.locations := by
  obtain ⟨context,owned⟩ := registered input protections selected head tail writable raw nodeTags
  refine ⟨context,?_⟩
  intro position valid positive lower upper
  obtain ⟨data⟩ := owned position valid positive lower upper
  exact ⟨data.base⟩
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedEntryData
