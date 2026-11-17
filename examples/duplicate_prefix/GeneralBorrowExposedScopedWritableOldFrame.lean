import duplicate_prefix.GeneralBorrowExposedScopedWritableSharedOld
import duplicate_prefix.GeneralBorrowExposedScopedWritableDefaultOld
import duplicate_prefix.GeneralBorrowExposedScopedWritableProtectedMutableOld
import duplicate_prefix.GeneralBorrowSifaWritableFrame
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableOldFrame
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSifaWritableFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- Full actual shared construction retains mixed old-leaf local Write inputs. -/
theorem shared (input : GeneralBorrowFreshMetadataChildShared.Input) (protections : ProtectedTags) (support : UniIndex→Prop)
    (present : ∀query,support query→∃node,input.tree.nodeAt query=some node)
    (notParent : ∀query,support query→query≠input.parent)
    (initial : GeneralRangeMapState.Every (Profile input.tree protections support) input.tree.locations) :
    GeneralRangeMapState.Every (Profile (GeneralBorrowFreshMetadataChildShared.result input) protections support)
      (GeneralBorrowFreshMetadataChildShared.result input).locations := by
  rw [GeneralBorrowFreshMetadataChildShared.tree_eq]
  exact sifa _ input.parent .Read protections support
    (GeneralBorrowExposedScopedWritableSharedOld.stage input protections support present notParent initial)

theorem mutable (input : GeneralBorrowFreshMetadataChildDefault.Input) (protections : ProtectedTags) (support : UniIndex→Prop)
    (present : ∀query,support query→∃node,input.tree.nodeAt query=some node)
    (notParent : ∀query,support query→query≠input.parent)
    (initial : GeneralRangeMapState.Every (Profile input.tree protections support) input.tree.locations) :
    GeneralRangeMapState.Every (Profile (GeneralBorrowFreshMetadataChildDefault.result input) protections support)
      (GeneralBorrowFreshMetadataChildDefault.result input).locations := by
  rw [GeneralBorrowFreshMetadataChildDefault.tree_eq]
  exact sifa _ input.parent .Read protections support
    (GeneralBorrowExposedScopedWritableDefaultOld.stage input protections support present notParent initial)

theorem protected_mutable (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags) (support : UniIndex→Prop)
    (present : ∀query,support query→∃node,input.tree.nodeAt query=some node)
    (notParent : ∀query,support query→query≠input.parent)
    (initial : GeneralRangeMapState.Every (Profile input.tree protections support) input.tree.locations) :
    GeneralRangeMapState.Every (Profile (GeneralBorrowFreshMetadataChildMutable.result input) protections support)
      (GeneralBorrowFreshMetadataChildMutable.result input).locations := by
  rw [GeneralBorrowFreshMetadataChildMutable.tree_eq]
  exact sifa _ input.parent .None protections support
    (GeneralBorrowExposedScopedWritableProtectedMutableOld.stage input protections support present notParent initial)
end DuplicatePrefix.GeneralBorrowExposedScopedWritableOldFrame
