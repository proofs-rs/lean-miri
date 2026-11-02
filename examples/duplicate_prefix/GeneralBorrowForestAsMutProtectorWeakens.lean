import duplicate_prefix.GeneralBorrowForestMutableAccess
import duplicate_prefix.GeneralBorrowFreshProtectorRelease
namespace DuplicatePrefix.GeneralBorrowForestAsMutProtectorWeakens
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
/-- Removing actual global protectors retains the full foreign support and both
cache-kind records, as well as the original mutable anchor's permissions. -/
def location (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (weaken : ∀ tag, after.contains tag = true → before.contains tag = true)
    (anchor primary : UniIndex) (extras : List UniIndex)
    (data : GeneralBorrowForestMutableAccess.Data tree location before anchor primary extras) :
    GeneralBorrowForestMutableAccess.Data tree location after anchor primary extras := by
  have owner := GeneralBorrowFreshProtectorRelease.location_weakens tree location before after weaken anchor .Write
    ⟨⟨data.base.forest⟩,data.base.owned⟩
  exact {
    base := {
      forest := data.base.forest
      owned := owner.2
      rootPath := data.base.rootPath
      region := {
        support := data.base.region.support
        present := data.base.region.present
        children := data.base.region.children
        unexposed := data.base.region.unexposed
        zero := data.base.region.zero
        owned := by
          intro index node member present
          exact GeneralBorrowPermissions.owned_release _ .ForeignAccess _ _ (weaken node.tag)
            (data.base.region.owned index node member present) }
      supported := data.base.supported
      foreignGraph := data.base.foreignGraph }
    readZero := data.readZero }
end DuplicatePrefix.GeneralBorrowForestAsMutProtectorWeakens
