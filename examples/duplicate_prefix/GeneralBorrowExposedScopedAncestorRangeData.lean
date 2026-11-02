import duplicate_prefix.GeneralBorrowExposedScopedAncestorReadFrame
import duplicate_prefix.GeneralBorrowExposedConstructorUnique
import duplicate_prefix.GeneralBorrowExposedKnownRootRangeData
namespace DuplicatePrefix.GeneralBorrowExposedScopedAncestorRangeData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowExposedKnownRootState
open GeneralBorrowExposedKnownRootRangeData (Context)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

set_option autoImplicit false in
structure Data (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop) where
  forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology
  component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology anchor.toNat
  supportEq : component.support=support
  owned : GeneralBorrowExposedScopedNormal.Owned (source_normal_projection tree location protections) anchor.toNat .Read component
  rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast!=selected.toNat
  ancestors : ∀ index node state,component.support index.toNat → tree.nodeAt index=some node →
    node.isExposed=true → tree.locationStateAt location index=some state →
    index.toNat ∈ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat ∧ state.permission=.Unique
  separate : ∀ index,area.support index → ¬component.support index.toNat
  coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections
  readable : Readable tree location protections
  primary : head≠selected → GeneralBorrowExposedKnownRootPrimaryWitness.Data tree location head protections
  virtual : ∀ root ∈ tail,root≠selected → GeneralBorrowExposedKnownRootState.Data tree location root protections

theorem initial {tree location protections anchor selected head tail support}
    (data : Data tree location protections anchor selected head tail support) :
    GeneralBorrowExposedConstructorUnique.Unique tree location support := by
  intro query node member present exposed
  have statePresent : tree.locationStateAt location query=some ((location.perms.get query).getD node.defaultLocationState) := by
    simp only [BorrowTree.locationStateAt,present,bind,pure,Option.bind_some]
  exact (data.ancestors query node _ (by rw [data.supportEq];exact member) present exposed statePresent).2

/-- Initial exposed-ancestor component data supplies the actual concrete Read
and retains its Unique permissions after every other-root callback. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop) (range : ByteRange)
    (context : Context tree anchor selected head tail)
    (data : Data tree location protections anchor selected head tail support) :
    source_access_status (source_tree_access_at tree location (some anchor) .Read protections .VisitChildrenOfAccessed range)=none ∧
    GeneralBorrowExposedConstructorUnique.Unique tree
      (source_access_location (source_tree_access_at tree location (some anchor) .Read protections .VisitChildrenOfAccessed range)) support := by
  obtain ⟨after,actual,status,_,_,_,keep⟩ := GeneralBorrowExposedScopedAncestorReadFrame.access tree location protections
    anchor selected head context.anchorNode context.selectedNode tail range context.roots data.forest data.component data.owned
    context.depth context.children context.anchorPresent context.selectedPresent data.rootPath data.ancestors data.separate
    data.coherent data.readable context.tags data.primary data.virtual
  refine ⟨status,?_⟩
  rw [actual]
  intro query node member present exposed
  have supported : data.component.support query.toNat := by rw [data.supportEq];exact member
  have outside : ¬area.support query := by intro inside;exact data.separate query inside supported
  have slot := keep query outside
  have finalPresent : tree.locationStateAt (tree.performNormalAccessAt location anchor .Read protections .VisitChildrenOfAccessed).location query=
      some ((after.perms.get query).getD node.defaultLocationState) := by
    simp only [BorrowTree.locationStateAt,present,bind,pure,Option.bind_some,slot]
  exact (GeneralBorrowExposedScopedAncestorPermission.preserves tree location protections anchor .Read .VisitChildrenOfAccessed
    data.forest data.component data.owned context.depth context.children context.anchorNode context.anchorPresent data.ancestors
    query node _ supported present exposed finalPresent).2
end DuplicatePrefix.GeneralBorrowExposedScopedAncestorRangeData
