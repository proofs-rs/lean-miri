import duplicate_prefix.GeneralBorrowExposedScopedInactiveRangeData
import duplicate_prefix.GeneralBorrowExposedScopedInactiveMixedAccess
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveMixedRangeData
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
its selected exposed-ancestor component. The other roots retain their conditional profiles. -/
structure Data (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop) (writable : Nat → Bool) where
  base : GeneralBorrowExposedScopedInactiveRangeData.Data tree location protections anchor selected head tail support
  support_eq : base.component.support = support
  mixed : Mixed tree location protections anchor support writable

def Post (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (support : Nat → Prop) (writable : Nat → Bool) : Prop :=
  GeneralBorrowExposureCardinality.LocationCoherent tree location protections ∧
    GeneralBorrowExposedKnownRootState.Readable tree location protections ∧
    GeneralBorrowExposedInactiveConstructor.Profile tree location anchor support ∧
    Mixed tree location protections anchor support writable

theorem initial {tree location protections anchor selected head tail support writable}
    (data : Data tree location protections anchor selected head tail support writable) :
    Post tree location protections anchor support writable :=
  ⟨data.base.coherent,data.base.readable,GeneralBorrowExposedScopedInactiveRangeData.initial data.base,data.mixed⟩

theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex)  (range : ByteRange)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (support : Nat → Prop) (writable : Nat → Bool) (fits : tree.nodes.data.size ≤ 4294967296)
    (data : Data tree location protections anchor selected head tail support writable) :
    source_access_status (source_tree_access_at tree location (some anchor) .Read protections .VisitChildrenOfAccessed range) = none ∧
      Post tree (source_access_location (source_tree_access_at tree location (some anchor) .Read protections .VisitChildrenOfAccessed range)) protections anchor support writable := by
  have base := GeneralBorrowExposedScopedInactiveRangeData.access tree location protections anchor selected head tail support range context data.base
  have callback := GeneralBorrowExposedScopedInactiveExposureReadFrame.access tree location protections anchor selected head context.anchorNode context.selectedNode tail
    range context.roots data.base.forest data.base.component data.base.owned context.depth context.children context.anchorPresent context.selectedPresent
    data.base.rootPath data.base.ancestors data.base.separate data.base.coherent data.base.readable context.tags data.base.primary data.base.virtual
  have mixed : GeneralBorrowExposedScopedOwnership.Pointwise data.base.component.support
      (source_normal_projection tree location protections) writable
      (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat) := by
    rw [data.support_eq]
    exact data.mixed
  obtain ⟨after,actual,status,preserved⟩ := GeneralBorrowExposedScopedInactiveMixedAccess.mixed tree location protections
    anchor selected head context.anchorNode context.selectedNode tail range context.roots data.base.forest data.base.component data.base.owned
    context.depth context.children context.anchorPresent context.selectedPresent data.base.rootPath data.base.ancestors data.base.separate
    data.base.coherent data.base.readable context.tags data.base.primary fits writable mixed data.base.virtual
  refine ⟨base.1,?_,?_,base.2,?_⟩
  · rw [callback.choose_spec.1]
    exact callback.choose_spec.2.2.2.2.1
  · rw [callback.choose_spec.1]
    exact callback.choose_spec.2.2.2.1
  · rw [actual]
    rw [data.support_eq] at preserved
    exact preserved

theorem post_map (tree : BorrowTree) (map : DedupRangeMap LocationTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (support : Nat → Prop) (writable : Nat → Bool) :
    Post {tree with locations := map} location protections anchor support writable = Post tree location protections anchor support writable := rfl
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveMixedRangeData
