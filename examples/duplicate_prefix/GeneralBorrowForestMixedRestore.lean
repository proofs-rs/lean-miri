import duplicate_prefix.GeneralBorrowForestMixedAccess
import duplicate_prefix.GeneralBorrowForestMutableAccess
import duplicate_prefix.GeneralBorrowFreshLifetimeRestore

namespace DuplicatePrefix.GeneralBorrowForestMixedRestore
open Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess

/-- After the actual shared lifetime's protector weakening, mixed Read/Write
labels recover the older mutable anchor's FULL records. The target's root-path
fact is graph metadata, and RestoreTo is discharged by the two actual shared
attachments and real endCall; no restored permission or operation success is
an input. Both cache kinds are retained on the unchanged foreign support. -/
def restore (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (weaken : ∀ tag, after.contains tag = true → before.contains tag = true)
    (child target primary : UniIndex) (extras : List UniIndex) (writable : Nat → Bool)
    (restoration : GeneralBorrowFreshLifetimeRestore.RestoreTo tree before after child target writable)
    (rootPath : ((source_normal_projection tree location before).topology.ancestorPath target.toNat).getLast! = primary.toNat)
    (data : GeneralBorrowForestMixedAccess.Data tree location before child primary extras writable) :
    GeneralBorrowForestMutableAccess.Data tree location after target primary extras := by
  have owner := GeneralBorrowFreshLifetimeRestore.restore_location tree location before after weaken
    child target writable restoration ⟨⟨⟨data.base.forest⟩,data.base.owned⟩,data.mixed⟩
  refine {
    base := {
      forest := data.base.forest
      owned := owner.2
      rootPath := rootPath
      region := {
        support := data.base.region.support
        present := data.base.region.present
        children := data.base.region.children
        unexposed := data.base.region.unexposed
        zero := data.writeZero
        owned := ?_ }
      supported := data.base.supported
      foreignGraph := ?_ }
    readZero := data.base.region.zero }
  · intro index node member present
    exact GeneralBorrowPermissions.owned_release _ .ForeignAccess _ _ (weaken node.tag)
      (data.base.region.owned index node member present)
  · intro index member localTarget
    change index.toNat ∈ (source_normal_projection tree location before).topology.ancestorPath target.toNat at localTarget
    have targetRelated : GeneralBorrowAnchor.relation (source_normal_projection tree location before) target.toNat index.toNat = .LocalAccess := by
      simp only [GeneralBorrowAnchor.relation,localTarget,↓reduceIte]
    have childRelated := (restoration.localRetained location index.toNat targetRelated).1
    have childLocal : index.toNat ∈ (source_normal_projection tree location before).topology.ancestorPath child.toNat := by
      unfold GeneralBorrowAnchor.relation at childRelated
      split at childRelated
      next found => exact found
      next => contradiction
    exact data.base.foreignGraph index member childLocal

end DuplicatePrefix.GeneralBorrowForestMixedRestore
