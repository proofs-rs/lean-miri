import duplicate_prefix.GeneralBorrowExposedKnownRootRangeData
import duplicate_prefix.GeneralBorrowExposedScopedMixedAccess
namespace DuplicatePrefix.GeneralBorrowExposedScopedMixedRangeData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def Mixed (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (support : Nat → Prop) (writable : Nat → Bool) : Prop :=
  GeneralBorrowExposedScopedOwnership.Pointwise support (source_normal_projection tree location protections) writable
    (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat)

/-- Raw location resources for the actual Read, with mixed ownership only in
its selected hidden component. The other roots retain their conditional profiles. -/
structure Data (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop) (writable : Nat → Bool) where
  base : GeneralBorrowExposedKnownRootRangeData.Data tree location protections anchor selected head tail .Read
  support_eq : base.component.support = support
  mixed : Mixed tree location protections anchor support writable

def Post (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (support : Nat → Prop) (writable : Nat → Bool) : Prop :=
  GeneralBorrowExposedKnownRootRangeData.Post .Read tree location protections ∧
    Mixed tree location protections anchor support writable

theorem initial {tree location protections anchor selected head tail support writable}
    (data : Data tree location protections anchor selected head tail support writable) :
    Post tree location protections anchor support writable :=
  ⟨GeneralBorrowExposedKnownRootRangeData.initial data.base,data.mixed⟩

theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (mode : ChildrenVisitMode) (range : ByteRange)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (support : Nat → Prop) (writable : Nat → Bool) (fits : tree.nodes.data.size ≤ 4294967296)
    (data : Data tree location protections anchor selected head tail support writable) :
    source_access_status (source_tree_access_at tree location (some anchor) .Read protections mode range) = none ∧
      Post tree (source_access_location (source_tree_access_at tree location (some anchor) .Read protections mode range)) protections anchor support writable := by
  have base := GeneralBorrowExposedKnownRootRangeData.access tree location protections anchor selected head tail .Read mode range context data.base
  have mixed : GeneralBorrowExposedScopedOwnership.Pointwise data.base.component.support
      (source_normal_projection tree location protections) writable
      (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat) := by
    rw [data.support_eq]
    exact data.mixed
  obtain ⟨after,actual,status,preserved⟩ := GeneralBorrowExposedScopedMixedAccess.mixed tree location protections
    anchor selected head context.anchorNode context.selectedNode tail mode range context.roots data.base.forest data.base.component data.base.owned
    context.depth context.children context.anchorPresent context.selectedPresent data.base.rootPath data.base.hidden data.base.separate
    data.base.coherent data.base.profile context.tags data.base.primary fits writable mixed data.base.virtual
  refine ⟨base.1,base.2,?_⟩
  rw [actual]
  rw [data.support_eq] at preserved
  exact preserved

theorem post_map (tree : BorrowTree) (map : DedupRangeMap LocationTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (support : Nat → Prop) (writable : Nat → Bool) :
    Post {tree with locations := map} location protections anchor support writable = Post tree location protections anchor support writable := rfl
end DuplicatePrefix.GeneralBorrowExposedScopedMixedRangeData
